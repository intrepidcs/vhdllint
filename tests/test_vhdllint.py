"""Tests for vhdllint.

Detection tests pin current (correct) behavior.
Tests marked xfail(strict=True) document known bugs: they fail today and
must XPASS (forcing marker removal) once the bug is fixed.
"""

import os
import subprocess
import sys
from pathlib import Path

import pytest

import vhdllint

ROOT = Path(__file__).resolve().parent.parent

HEADER = (
	"-- Copyright 2026 Example Corp\n"
	"-- Test design\n"
	"\n"
	"library ieee;\n"
	"use ieee.std_logic_1164.all;\n"
	"\n"
)

DEFAULT_PORTS = (
	"    clk_i : in std_logic;\n"
	"    d_i : in std_logic;\n"
	"    q_o : out std_logic\n"
)

DEFAULT_BODY = (
	"  process(clk_i)\n"
	"  begin\n"
	"    if rising_edge(clk_i) then\n"
	"      q_o <= d_i;\n"
	"    end if;\n"
	"  end process;\n"
)


def design(decls="", body=DEFAULT_BODY, ports=DEFAULT_PORTS):
	"""Build a complete, style-clean VHDL design around the given fragments."""
	return (
		HEADER
		+ "entity test is\n"
		+ "  port (\n"
		+ ports
		+ "  );\n"
		+ "end entity test;\n"
		+ "\n"
		+ "architecture rtl of test is\n"
		+ "\n"
		+ decls
		+ "\n"
		+ "begin\n"
		+ "\n"
		+ body
		+ "\n"
		+ "end architecture rtl;\n"
	)


def lint(source, filename="test.vhd"):
	"""Run all lint checks, returning (line, category, confidence, message) tuples."""
	errors = []

	def collector(_filename, lineref, category, confidence, message):
		errors.append((lineref.Line(), category, confidence, message))

	vhdllint.ProcessFileData(filename, "vhd", source.split("\n"), collector)
	return errors


def categories(errors):
	return {category for _, category, _, _ in errors}


# ---------------------------------------------------------------------------
# Detection tests: current behavior that must keep working
# ---------------------------------------------------------------------------

def test_clean_design_no_errors():
	assert lint(design()) == []


def test_missing_copyright():
	source = "-- Header only, no legal notice\n\nentity test is\nend entity test;\n"
	assert "legal/copyright" in categories(lint(source))


def test_missing_header():
	source = "library ieee;\nuse ieee.std_logic_1164.all;\n"
	assert "readability/header" in categories(lint(source))


def test_tab_reported_with_line_number():
	source = HEADER + "\tentity test is\nend entity test;\n"
	errors = [e for e in lint(source) if e[1] == "whitespace/tab"]
	assert errors
	assert errors[0][0] == 7  # 1-based line of the tab


def test_trailing_whitespace():
	source = HEADER + "entity test is  \nend entity test;\n"
	assert "whitespace/end_of_line" in categories(lint(source))


def test_missing_newline_at_eof():
	source = HEADER + "entity test is\nend entity test;"
	assert "whitespace/ending_newline" in categories(lint(source))


def test_line_length():
	source = HEADER + "-- " + "x" * 100 + "\n"
	assert "whitespace/line_length" in categories(lint(source))


def test_deprecated_package():
	source = HEADER + "use ieee.std_logic_arith.all;\n"
	assert "build/deprecated" in categories(lint(source))


def test_time_units_missing_space():
	source = HEADER + "-- placeholder\nwait for 10ns;\n"
	assert "readability/units" in categories(lint(source))


def test_others_instead_of_hex_zero():
	source = design(
		decls="  signal v_s : std_logic_vector(7 downto 0);\n",
		body="  v_s <= x\"00\";\n",
	)
	assert "readability/others" in categories(lint(source))


def test_redundant_boolean_equality():
	body = (
		"  process(en_s)\n"
		"  begin\n"
		"    if en_s = true then\n"
		"      q_o <= d_i;\n"
		"    end if;\n"
		"  end process;\n"
	)
	source = design(decls="  signal en_s : boolean;\n", body=body)
	assert "readability/booleans" in categories(lint(source))


def test_multiple_declarations_per_line():
	source = design(decls="  signal a_s, b_s : std_logic;\n")
	assert "readability/declarations" in categories(lint(source))


def test_constant_naming_conventions():
	no_prefix = design(decls="  constant BAD : integer := 5;\n")
	assert "readability/naming" in categories(lint(no_prefix))

	lowercase = design(decls="  constant c_bad : integer := 5;\n")
	assert "readability/constants" in categories(lint(lowercase))


def test_signal_capitalization():
	source = design(decls="  signal Bad_Sig : std_logic;\n")
	assert "readability/identifiers" in categories(lint(source))


@pytest.mark.parametrize("stype", ["integer", "natural", "positive"])
def test_integer_types_without_range(stype):
	source = design(decls="  signal cnt_s : %s;\n" % stype)
	assert "runtime/integers" in categories(lint(source))


@pytest.mark.parametrize("stype", ["integer", "natural", "positive"])
def test_integer_types_with_range_ok(stype):
	source = design(decls="  signal cnt_s : %s range 0 to 7;\n" % stype)
	assert "runtime/integers" not in categories(lint(source))


def test_record_fields_nolint_integers_not_misattributed(capsys):
	decls = (
		"  type test_cfg_t is record\n"
		"    tdata_width        : natural;       -- NOLINT(runtime/integers)\n"
		"    rx_fifo_size_bytes : natural;       -- NOLINT(runtime/integers)\n"
		"    enable_cdc         : boolean;\n"
		"  end record;\n"
	)
	source = design(decls=decls)

	vhdllint._lint_state.ResetErrorCounts()
	vhdllint.ProcessFileData("test.vhd", "vhd", source.split("\n"), vhdllint.Error)
	err = capsys.readouterr().err
	assert "runtime/integers" not in err


def test_unused_signal():
	source = design(decls="  signal unused_s : std_logic;\n")
	errors = [e for e in lint(source) if e[1] == "build/unused"]
	assert any("unused_s" in message for _, _, _, message in errors)


def test_missing_signal_in_sensitivity_list():
	decls = (
		"  signal a_s : std_logic;\n"
		"  signal b_s : std_logic;\n"
		"  signal y_s : std_logic;\n"
	)
	body = (
		"  process(a_s)\n"
		"  begin\n"
		"    y_s <= a_s and b_s;\n"
		"  end process;\n"
	)
	errors = [e for e in lint(design(decls=decls, body=body))
			  if e[1] == "runtime/sensitivity"]
	assert any("b_s" in message for _, _, _, message in errors)


def test_clk_event_flagged():
	body = (
		"  process(clk_i)\n"
		"  begin\n"
		"    if clk_i'event and clk_i = '1' then\n"
		"      q_o <= d_i;\n"
		"    end if;\n"
		"  end process;\n"
	)
	assert "runtime/rising_edge" in categories(lint(design(body=body)))


def test_positional_port_map():
	body = (
		"  u0 : entity work.sub\n"
		"    port map (\n"
		"      clk_i,\n"
		"      d_i\n"
		"    );\n"
	)
	assert "readability/portmaps" in categories(lint(design(body=body)))


def test_inferred_latch():
	source = design(body="  q_o <= d_i when clk_i = '1';\n")
	assert "runtime/latches" in categories(lint(source))


def test_invalid_port_type():
	ports = (
		"    clk_i : in std_logic;\n"
		"    d_i : in bit;\n"
		"    q_o : out std_logic\n"
	)
	assert "build/port_types" in categories(lint(design(ports=ports)))


def test_multiple_drivers():
	decls = "  signal x_s : std_logic;\n"
	body = (
		"  process(clk_i)\n"
		"  begin\n"
		"    if rising_edge(clk_i) then\n"
		"      x_s <= d_i;\n"
		"    end if;\n"
		"  end process;\n"
		"\n"
		"  process(clk_i)\n"
		"  begin\n"
		"    if rising_edge(clk_i) then\n"
		"      x_s <= not d_i;\n"
		"    end if;\n"
		"  end process;\n"
	)
	assert "runtime/multiple_drivers" in categories(lint(design(decls=decls, body=body)))


def test_component_declaration_flagged():
	decls = (
		"  component sub\n"
		"    port (\n"
		"      x : in std_logic\n"
		"    );\n"
		"  end component;\n"
	)
	assert "readability/components" in categories(lint(design(decls=decls)))


def test_process_all_flagged():
	body = (
		"  process(all)\n"
		"  begin\n"
		"    q_o <= d_i;\n"
		"  end process;\n"
	)
	assert "build/vhdl2008/sensitivity" in categories(lint(design(body=body)))


def test_comment_missing_space():
	source = HEADER + "--bad comment\nentity test is\nend entity test;\n"
	assert "whitespace/comments" in categories(lint(source))


def test_redundant_fsm_state_assignment():
	decls = (
		"  type state_t is (ST_A, ST_B);\n"
		"  signal state : state_t;\n"
	)
	body = (
		"  process(clk_i)\n"
		"  begin\n"
		"    if rising_edge(clk_i) then\n"
		"      case state is\n"
		"        when ST_A =>\n"
		"          state <= ST_A;\n"
		"        when others =>\n"
		"          state <= ST_A;\n"
		"      end case;\n"
		"    end if;\n"
		"  end process;\n"
	)
	assert "readability/fsm" in categories(lint(design(decls=decls, body=body)))


def test_nolint_suppression(capsys):
	base = HEADER + "entity test is\nend entity test;\n"
	with_tab = base.replace("entity test is", "\tentity test is")
	suppressed = base.replace(
		"entity test is", "\tentity test is  -- NOLINT(whitespace/tab)")

	vhdllint._lint_state.ResetErrorCounts()
	lint_via_error = lambda src: vhdllint.ProcessFileData(
		"test.vhd", "vhd", src.split("\n"), vhdllint.Error)

	lint_via_error(with_tab)
	assert "whitespace/tab" in capsys.readouterr().err

	lint_via_error(suppressed)
	assert "whitespace/tab" not in capsys.readouterr().err


def test_cli_end_to_end(tmp_path):
	bad = tmp_path / "bad.vhd"
	bad.write_text("entity bad is\nend entity bad;\n")
	result = subprocess.run(
		[sys.executable, str(ROOT / "vhdllint.py"), str(bad)],
		capture_output=True, text=True)
	assert result.returncode == 1
	assert "legal/copyright" in result.stderr


def test_cli_nonascii_output_does_not_crash(tmp_path):
	bad = tmp_path / "bäd.vhd"
	bad.write_text("entity bad is\nend entity bad;\n")
	env = dict(os.environ, PYTHONIOENCODING="ascii")
	result = subprocess.run(
		[sys.executable, str(ROOT / "vhdllint.py"), str(bad)],
		capture_output=True, text=True, env=env,
		encoding="utf-8", errors="replace")
	assert "Traceback" not in result.stderr
	assert result.returncode == 1
	assert "legal/copyright" in result.stderr


# ---------------------------------------------------------------------------
# False-positive guards: near-miss inputs that must NOT be flagged
# ---------------------------------------------------------------------------

def test_boolean_equality_in_comment_not_flagged():
	source = design(decls="  -- set enable = true for fast mode\n")
	assert "readability/booleans" not in categories(lint(source))


def test_time_units_in_comment_not_flagged():
	source = design(decls="  -- resolution is 10ns per tick\n")
	assert "readability/units" not in categories(lint(source))


def test_hex_zero_in_comment_not_flagged():
	source = design(decls="  -- reset value is x\"00\"\n")
	assert "readability/others" not in categories(lint(source))


def test_conforming_constant_not_flagged():
	source = design(decls="  constant C_WIDTH : integer := 8;\n")
	cats = categories(lint(source))
	assert "readability/naming" not in cats
	assert "readability/constants" not in cats


def test_clocked_process_exempt_from_sensitivity_check():
	decls = (
		"  signal a_s : std_logic;\n"
		"  signal b_s : std_logic;\n"
	)
	body = (
		"  process(clk_i)\n"
		"  begin\n"
		"    if rising_edge(clk_i) then\n"
		"      q_o <= a_s and b_s;\n"
		"    end if;\n"
		"  end process;\n"
	)
	assert "runtime/sensitivity" not in categories(lint(design(decls=decls, body=body)))


def test_when_with_else_not_a_latch():
	decls = "  signal sel_s : std_logic;\n"
	source = design(decls=decls, body="  q_o <= d_i when sel_s = '1' else '0';\n")
	assert "runtime/latches" not in categories(lint(source))


def test_named_port_map_not_flagged():
	body = (
		"  u0 : entity work.sub\n"
		"    port map (\n"
		"      x_i => clk_i,\n"
		"      y_i => d_i\n"
		"    );\n"
	)
	assert "readability/portmaps" not in categories(lint(design(body=body)))


def test_output_port_name_inside_report_string_not_flagged_as_read():
	ports = (
		"    overflow : out std_logic := '0';\n"
		"    q_o : out std_logic\n"
	)
	decls = "  signal overflow_reg : std_logic;\n"
	body = (
		"  process(all)\n"
		"  begin\n"
		"    if true then\n"
		"      assert overflow_reg /= '1'\n"
		"        report \"overflow should never occur in this mode\"\n"
		"        severity failure;\n"
		"    end if;\n"
		"  end process;\n"
	)
	assert "build/vhdl2008/outputs" not in categories(lint(design(decls=decls, body=body, ports=ports)))


def test_comb_process_default_assignment_not_combinational_loop():
	decls = (
		"  signal i_shift_storage : std_logic;\n"
		"  signal s_axis_tvalid : std_logic;\n"
		"  signal i_hold_input : std_logic;\n"
		"  signal i_clear_storage : std_logic;\n"
		"  signal n : std_logic_vector(3 downto 0);\n"
		"  signal q : std_logic_vector(3 downto 0);\n"
	)
	body = (
		"  comb_proc : process (all)\n"
		"  begin\n"
		"    n <= q;\n"
		"\n"
		"    if i_shift_storage = '1' then\n"
		"      n(0) <= '0';\n"
		"      n(3 downto 1) <= q(2 downto 0);\n"
		"    end if;\n"
		"\n"
		"    if i_shift_storage = '1' and s_axis_tvalid = '1' and i_hold_input = '0' then\n"
		"      n(0) <= '1';\n"
		"    end if;\n"
		"\n"
		"    if i_clear_storage = '1' then\n"
		"      n <= (others => '0');\n"
		"    end if;\n"
		"  end process comb_proc;\n"
	)
	assert "runtime/combinational_loop" not in categories(lint(design(decls=decls, body=body)))


def test_comb_process_record_field_writes_not_combinational_loop():
	decls = (
		"  constant g_num_reg_stages : integer := 4;\n"
		"  type axis_word_t is record\n"
		"    tdata : std_logic;\n"
		"    tkeep : std_logic;\n"
		"    tlast : std_logic;\n"
		"    tvalid : std_logic;\n"
		"  end record;\n"
		"  type axis_word_arr_t is array (0 to g_num_reg_stages - 1) of axis_word_t;\n"
		"  constant c_axis_word : axis_word_t := (\n"
		"    tdata => '0',\n"
		"    tkeep => '0',\n"
		"    tlast => '0',\n"
		"    tvalid => '0'\n"
		"  );\n"
		"  signal i_shift_storage : std_logic;\n"
		"  signal s_axis_tvalid : std_logic;\n"
		"  signal i_hold_input : std_logic;\n"
		"  signal i_clear_storage : std_logic;\n"
		"  signal s_axis_tdata : std_logic;\n"
		"  signal s_axis_tkeep : std_logic;\n"
		"  signal s_axis_tlast : std_logic;\n"
		"  signal n : axis_word_arr_t;\n"
		"  signal q : axis_word_arr_t;\n"
	)
	body = (
		"  comb_proc : process (all)\n"
		"  begin\n"
		"\n"
		"    n <= q;\n"
		"\n"
		"    if i_shift_storage = '1' then\n"
		"      n(0) <= c_axis_word;\n"
		"      n(1 to g_num_reg_stages - 1) <= q(0 to g_num_reg_stages - 2);\n"
		"    end if;\n"
		"\n"
		"    if i_shift_storage = '1' and s_axis_tvalid = '1' and i_hold_input = '0' then\n"
		"      n(0).tdata <= s_axis_tdata;\n"
		"      n(0).tkeep <= s_axis_tkeep;\n"
		"      n(0).tlast <= s_axis_tlast;\n"
		"      n(0).tvalid <= '1';\n"
		"    end if;\n"
		"\n"
		"    if i_clear_storage = '1' then\n"
		"      for i in 0 to g_num_reg_stages - 1 loop\n"
		"        n(i) <= c_axis_word;\n"
		"      end loop;\n"
		"    end if;\n"
		"\n"
		"  end process comb_proc;\n"
	)
	assert "runtime/combinational_loop" not in categories(lint(design(decls=decls, body=body)))


def test_comment_divider_not_flagged():
	source = design(decls="  ----------------------------------------\n")
	assert "whitespace/comments" not in categories(lint(source))


def test_signal_used_only_in_port_map_not_unused():
	decls = "  signal x_s : std_logic;\n"
	body = (
		"  u0 : entity work.sub\n"
		"    port map (\n"
		"      y_o => x_s\n"
		"    );\n"
	)
	errors = [e for e in lint(design(decls=decls, body=body))
			  if e[1] == "build/unused"]
	assert not any("x_s" in message for _, _, _, message in errors)


def test_local_constant_used_only_between_attribute_ticks_not_unused():
	# C_AFTER_LENGTH is only referenced between two 'high attribute ticks on
	# the same line. The identifier scanner must not mistake the attribute
	# ticks for a paired quoted string and skip everything between them.
	decls = (
		"  type byte_arr_t is array (natural range <>) of std_logic;\n"
		"\n"
		"  function remove_range (\n"
		"    arr         : byte_arr_t;\n"
		"    start_index : natural;\n"
		"    end_index   : natural\n"
		"  ) return byte_arr_t is\n"
		"    constant C_BEFORE_LENGTH : natural := start_index;\n"
		"    constant C_AFTER_LENGTH  : natural := arr'high - end_index;\n"
		"    variable result          : byte_arr_t(arr'low to arr'high-(end_index-start_index)-1);\n"
		"  begin\n"
		"    result(result'low to C_BEFORE_LENGTH-1)             := arr(arr'low to C_BEFORE_LENGTH-1);\n"
		"    result(result'high-C_AFTER_LENGTH+1 to result'high) := arr(end_index+1 to arr'high);\n"
		"    return result;\n"
		"  end function remove_range;\n"
	)
	errors = [e for e in lint(design(decls=decls)) if e[1] == "build/unused"]
	assert not any("C_AFTER_LENGTH" in message for _, _, _, message in errors)


def test_single_process_two_writes_not_multiple_drivers():
	decls = "  signal x_s : std_logic;\n"
	body = (
		"  process(clk_i)\n"
		"  begin\n"
		"    if rising_edge(clk_i) then\n"
		"      if d_i = '1' then\n"
		"        x_s <= '0';\n"
		"      else\n"
		"        x_s <= '1';\n"
		"      end if;\n"
		"    end if;\n"
		"  end process;\n"
	)
	assert "runtime/multiple_drivers" not in categories(lint(design(decls=decls, body=body)))


# ---------------------------------------------------------------------------
# Multi-line statements: checks must work without pre-beautified input
# ---------------------------------------------------------------------------

def test_fsm_detection_with_arrow_on_next_line():
	decls = (
		"  type state_t is (ST_A, ST_B);\n"
		"  signal state : state_t;\n"
	)
	body = (
		"  process(clk_i)\n"
		"  begin\n"
		"    if rising_edge(clk_i) then\n"
		"      case state is\n"
		"        when ST_A\n"
		"          =>\n"
		"          state <= ST_A;\n"
		"        when others =>\n"
		"          state <= ST_A;\n"
		"      end case;\n"
		"    end if;\n"
		"  end process;\n"
	)
	assert "readability/fsm" in categories(lint(design(decls=decls, body=body)))


def test_latch_detected_in_split_assignment():
	body = (
		"  q_o <= d_i\n"
		"    when clk_i = '1';\n"
	)
	assert "runtime/latches" in categories(lint(design(body=body)))


def test_boolean_equality_detected_across_lines():
	body = (
		"  process(en_s)\n"
		"  begin\n"
		"    if en_s =\n"
		"      true then\n"
		"      q_o <= d_i;\n"
		"    end if;\n"
		"  end process;\n"
	)
	source = design(decls="  signal en_s : boolean;\n", body=body)
	assert "readability/booleans" in categories(lint(source))


def test_signal_used_in_split_assignment_not_unused():
	decls = "  signal x_s : std_logic;\n"
	body = (
		"  process(clk_i)\n"
		"  begin\n"
		"    if rising_edge(clk_i) then\n"
		"      q_o <=\n"
		"        d_i and x_s;\n"
		"      x_s <= d_i;\n"
		"    end if;\n"
		"  end process;\n"
	)
	errors = [e for e in lint(design(decls=decls, body=body))
			  if e[1] == "build/unused"]
	assert not any("x_s" in message for _, _, _, message in errors)


# ---------------------------------------------------------------------------
# Known-bug regression tests: xfail today, must XPASS after the fix
# ---------------------------------------------------------------------------

def test_match_search_cache_flag_collision():
	pattern = r"zz_cache_probe"
	vhdllint._regexp_compile_cache.clear()
	assert vhdllint.Match(pattern, "ZZ_CACHE_PROBE")  # Match is case-insensitive

	vhdllint._regexp_compile_cache.clear()
	vhdllint.Search(pattern, "zz_cache_probe")  # must not poison Match's cache entry
	assert vhdllint.Match(pattern, "ZZ_CACHE_PROBE")


def test_fsm_case_arrow_on_next_line_does_not_crash():
	decls = (
		"  type state_t is (ST_A, ST_B);\n"
		"  signal state : state_t;\n"
	)
	body = (
		"  process(clk_i)\n"
		"  begin\n"
		"    if rising_edge(clk_i) then\n"
		"      case state is\n"
		"        when ST_A\n"
		"          =>\n"
		"          state <= ST_B;\n"
		"        when others =>\n"
		"          state <= ST_A;\n"
		"      end case;\n"
		"    end if;\n"
		"  end process;\n"
	)
	lint(design(decls=decls, body=body))  # must not raise


def test_malformed_names_do_not_crash():
	# regex metachars in captured names must not reach re.compile
	source = HEADER + (
		"entity foo( is\n"
		"end entity foo(;\n"
		"\n"
		"architecture a( of foo( is\n"
		"begin\n"
		"end architecture a(;\n"
	)
	lint(source)  # must not raise
