#!/usr/bin/env python
#
# Copyright (c) 2009 Google Inc. All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
#    * Redistributions of source code must retain the above copyright
# notice, this list of conditions and the following disclaimer.
#    * Redistributions in binary form must reproduce the above
# copyright notice, this list of conditions and the following disclaimer
# in the documentation and/or other materials provided with the
# distribution.
#    * Neither the name of Google Inc. nor the names of its
# contributors may be used to endorse or promote products derived from
# this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import codecs
import copy
import getopt
import glob
import itertools
import math  # for log
import os
import re
import sre_compile
import string
import sys
import sysconfig
import unicodedata
import xml.etree.ElementTree
from collections import Counter
from collections import OrderedDict
from pathlib import Path

# if empty, use defaults
_valid_extensions = set([])

__VERSION__ = '0.0.1'

xrange = range  # Python 3

_USAGE = """
Syntax: vhdllint.py [--verbose=#] [--output=emacs|eclipse|vs7|junit|sed|gsed]
				   [--filter=-x,+y,...]
				   [--counting=total|toplevel|detailed] [--root=subdir]
				   [--repository=path]
				   [--linelength=digits]
				   [--recursive]
				   [--exclude=path]
				   [--extensions=vhd,vhdl,...]
				   [--quiet]
				   [--version]
		<file> [file] ...
  Style checker for VHDL source files.
  This is a fork of the Google style checker with minor extensions.
  The style guidelines this tries to follow are those in
	https://google.github.io/styleguide/cppguide.html
  Every problem is given a confidence score from 1-5, with 5 meaning we are
  certain of the problem, and 1 meaning it could be a legitimate construct.
  This will miss some errors, and is not a substitute for a code review.
  To suppress false-positive errors of a certain category, add a
  'NOLINT(category)' comment to the line.  NOLINT or NOLINT(*)
  suppresses errors of all categories on that line. To suppress errors on
  the following line, add a comment 'NOLINTNEXTLINE(category)'. To suppress
  errors for a region, add comment 'NOLINTBEGIN(category)' above the
  region and 'NOLINTEND(category)' below the region.
  The files passed in will be linted; at least one file must be provided.
  Default linted extensions are %s.
  Other file types will be ignored.
  Change the extensions with the --extensions flag.
  Flags:
	output=emacs|eclipse|vs7|junit|sed|gsed
	  By default, the output is formatted to ease emacs parsing.  Visual Studio
	  compatible output (vs7) may also be used.  Further support exists for
	  eclipse (eclipse), and JUnit (junit). XML parsers such as those used
	  in Jenkins and Bamboo may also be used.
	  The sed format outputs sed commands that should fix some of the errors.
	  Note that this requires gnu sed. If that is installed as gsed on your
	  system (common e.g. on macOS with homebrew) you can use the gsed output
	  format. Sed commands are written to stdout, not stderr, so you should be
	  able to pipe output straight to a shell to run the fixes.
	verbose=#
	  Specify a number 0-5 to restrict errors to certain verbosity levels.
	  Errors with lower verbosity levels have lower confidence and are more
	  likely to be false positives.
	quiet
	  Don't print anything if no errors are found.
	filter=-x,+y,...
	  Specify a comma-separated list of category-filters to apply: only
	  error messages whose category names pass the filters will be printed.
	  (Category names are printed with the message and look like
	  "[whitespace/indent]".)  Filters are evaluated left to right.
	  "-FOO" and "FOO" means "do not print categories that start with FOO".
	  "+FOO" means "do print categories that start with FOO".
	  Examples: --filter=-whitespace,+whitespace/braces
				--filter=whitespace,runtime/printf,+runtime/printf_format
				--filter=-,+build/include_what_you_use
	  To see a list of all the categories used in vhdllint, pass no arg:
		 --filter=
	counting=total|toplevel|detailed
	  The total number of errors found is always printed. If
	  'toplevel' is provided, then the count of errors in each of
	  the top-level categories like 'build' and 'whitespace' will
	  also be printed. If 'detailed' is provided, then a count
	  is provided for each category like 'build/class'.
	repository=path
	  The top level directory of the repository, used to derive the header
	  guard CPP variable. By default, this is determined by searching for a
	  path that contains .git, .hg, or .svn. When this flag is specified, the
	  given path is used instead. This option allows the header guard CPP
	  variable to remain consistent even if members of a team have different
	  repository root directories (such as when checking out a subdirectory
	  with SVN). In addition, users of non-mainstream version control systems
	  can use this flag to ensure readable header guard CPP variables.
	  Examples:
		Assuming that Alice checks out ProjectName and Bob checks out
		ProjectName/trunk and trunk contains src/chrome/ui/browser.h, then
		with no --repository flag, the header guard CPP variable will be:
		Alice => TRUNK_SRC_CHROME_BROWSER_UI_BROWSER_H_
		Bob   => SRC_CHROME_BROWSER_UI_BROWSER_H_
		If Alice uses the --repository=trunk flag and Bob omits the flag or
		uses --repository=. then the header guard CPP variable will be:
		Alice => SRC_CHROME_BROWSER_UI_BROWSER_H_
		Bob   => SRC_CHROME_BROWSER_UI_BROWSER_H_
	root=subdir
	  The root directory used for deriving header guard CPP variable.
	  This directory is relative to the top level directory of the repository
	  which by default is determined by searching for a directory that contains
	  .git, .hg, or .svn but can also be controlled with the --repository flag.
	  If the specified directory does not exist, this flag is ignored.
	  Examples:
		Assuming that src is the top level directory of the repository (and
		cwd=top/src), the header guard CPP variables for
		src/chrome/browser/ui/browser.h are:
		No flag => CHROME_BROWSER_UI_BROWSER_H_
		--root=chrome => BROWSER_UI_BROWSER_H_
		--root=chrome/browser => UI_BROWSER_H_
		--root=.. => SRC_CHROME_BROWSER_UI_BROWSER_H_
	linelength=digits
	  This is the allowed line length for the project. The default value is
	  80 characters.
	  Examples:
		--linelength=120
	recursive
	  Search for files to lint recursively. Each directory given in the list
	  of files to be linted is replaced by all files that descend from that
	  directory. Files with extensions not in the valid extensions list are
	  excluded.
	exclude=path
	  Exclude the given path from the list of files to be linted. Relative
	  paths are evaluated relative to the current directory and shell globbing
	  is performed. This flag can be provided multiple times to exclude
	  multiple files.
	  Examples:
		--exclude=one.vhd
		--exclude=src/*.vhd
		--exclude=src/**/*.vhd --exclude=test/*.vhd
	extensions=extension,extension,...
	  The allowed file extensions that vhdllint will check
	  Examples:
		--extensions=%s
	vhdllint.py supports per-directory configurations specified in VHDLLINT.cfg
	files. VHDLLINT.cfg file can contain a number of key=value pairs.
	Currently the following options are supported:
	  set noparent
	  filter=+filter1,-filter2,...
	  exclude_files=regex
	  linelength=80
	  root=subdir
	  headers=x,y,...
	"set noparent" option prevents vhdllint from traversing directory tree
	upwards looking for more .cfg files in parent directories. This option
	is usually placed in the top-level project directory.
	The "filter" option is similar in function to --filter flag. It specifies
	message filters in addition to the |_DEFAULT_FILTERS| and those specified
	through --filter command-line flag.
	"exclude_files" allows to specify a regular expression to be matched against
	a file name. If the expression matches, the file is skipped and not run
	through the linter.
	"linelength" allows to specify the allowed line length for the project.
	The "root" option is similar in function to the --root flag (see example
	above). Paths are relative to the directory of the VHDLLINT.cfg.
	VHDLLINT.cfg has an effect on files in the same directory and all
	sub-directories, unless overridden by a nested configuration file.
	  Example file:
		filter=-build/include_order,+build/include_alpha
		exclude_files=.*\\.vhd
	The above example disables build/include_order warning and enables
	build/include_alpha as well as excludes all .vhd from being
	processed by linter, in the current directory (where the .cfg
	file is located) and all sub-directories.
"""

_signal_identifiers = {}
_constant_identifiers = {}
_local_identifiers = []
_other_identifiers = {}
_all_identifiers = OrderedDict()
_drivers = set()

# Commands for sed to fix the problem
_SED_FIXUPS = {
  'Remove spaces around =': r's/ = /=/',
  'Remove spaces around !=': r's/ != /!=/',
  'Remove space before ( in if (': r's/if (/if(/',
  'Remove space before ( in for (': r's/for (/for(/',
  'Remove space before ( in while (': r's/while (/while(/',
  'Remove space before ( in switch (': r's/switch (/switch(/',
  'Should have a space between // and comment': r's/\/\//\/\/ /',
  'Missing space before {': r's/\([^ ]\){/\1 {/',
  'Tab found, replace by spaces': r's/\t/  /g',
  'Line ends in whitespace.  Consider deleting these extra spaces.': r's/\s*$//',
  'You don\'t need a ; after a }': r's/};/}/',
  'Missing space after ,': r's/,\([^ ]\)/, \1/g',
}

_regexp_compile_cache = {}

# {str, set(int)}: a map from error categories to sets of linenumbers
# on which those errors are expected and should be suppressed.
_error_suppressions = {}
_error_suppressions_region = set()

# The root directory used for deriving header guard CPP variable.
# This is set by --root flag.
_root = None
_root_debug = False

# The top level repository directory. If set, _root is calculated relative to
# this directory instead of the directory containing version control artifacts.
# This is set by the --repository flag.
_repository = None

# Files to exclude from linting. This is set by the --exclude flag.
_excludes = None

# Whether to supress all PrintInfo messages, UNRELATED to --quiet flag
_quiet = False

# The allowed line length of files.
# This is set by --linelength flag.
_line_length = 80

if sys.version_info < (3,):
	# 	-- pylint: disable=no-member
	# BINARY_TYPE = str
	itervalues = dict.itervalues
	iteritems = dict.iteritems
else:
	# BINARY_TYPE = bytes
	itervalues = dict.values
	iteritems = dict.items


def unicode_escape_decode(x):
	if sys.version_info < (3,):
		return codecs.unicode_escape_decode(x)[0]
	else:
		return x


# {str, bool}: a map from error categories to booleans which indicate if the
# category should be suppressed for every line.
_global_error_suppressions = {}

# keywords to use with --outputs which generate stdout for machine processing
_MACHINE_OUTPUTS = [
  'junit',
  'sed',
  'gsed'
]

# We categorize each error message we print.  Here are the categories.
# We want an explicit list so we can list them all in vhdllint --filter=.
# If you add a new error message with a new category, add it to the list
# here!  vhdllint_unittest.py should tell you if you forget to do this.
_ERROR_CATEGORIES = [
		'build/arithmetic',
		'build/deprecated',
		'build/filename',
		'build/include_alpha',
		'build/port_modes',
		'build/port_types',
		'build/shadow',
		'build/unused',
		'build/vhdl2008',
		'build/vhdl2008/sensitivity',
		'build/vhdl2008/outputs',
		'legal/copyright',
		'readability/booleans',
		'readability/capitalization',
		'readability/constants',
		'readability/declarations',
		'readability/components',
		'readability/fsm',
		'readability/header',
		'readability/identifiers',
		'readability/multiline_comment',
		'readability/naming',
		'readability/nolint',
		'readability/nul',
		'readability/others',
		'readability/portmaps',
		'readability/reserved',
		'readability/todo',
		'readability/units',
		'readability/utf8',
		'runtime/combinational_loop',
		'runtime/integers',
		'runtime/latches',
		'runtime/loops',
		'runtime/multiple_drivers',
		'runtime/rising_edge',
		'runtime/sensitivity',
		'runtime/variables',
		'whitespace/blank_line',
		'whitespace/comments',
		'whitespace/end_of_line',
		'whitespace/ending_newline',
		'whitespace/indent',
		'whitespace/line_length',
		'whitespace/newline',
		'whitespace/tab',
		'whitespace/todo',
		]

# The default state of the category filter. This is overridden by the --filter=
# flag. By default all errors are on, so only add here categories that should be
# off by default (i.e., categories that must be enabled by the --filter= flags).
# All entries here should start with a '-' or '+', as in the --filter= flag.
_DEFAULT_FILTERS = ['-build/include_alpha']

# List of all reserved words in VHDL
_VHDL_RESERVED = [
	'abs',
	'access',
	'after',
	'alias',
	'all',
	'and',
	'architecture',
	'array',
	'assert',
	'attribute',
	'begin',
	'block',
	'body',
	'buffer',
	'bus',
	'case',
	'component',
	'configuration',
	'constant',
	'disconnect',
	'downto',
	'else',
	'elsif',
	'end',
	'entity',
	'exit',
	'file',
	'for',
	'function',
	'generate',
	'generic',
	'group',
	'guarded',
	'if',
	'impure',
	'in',
	'inertial',
	'inout',
	'is',
	'label',
	'library',
	'linkage',
	'literal',
	'loop',
	'map',
	'mod',
	'nand',
	'new',
	'next',
	'nor',
	'not',
	'null',
	'of',
	'on',
	'open',
	'or',
	'others',
	'out',
	'package',
	'port',
	'postponed',
	'procedure',
	'process',
	'pure',
	'range',
	'record',
	'register',
	'reject',
	'rem',
	'report',
	'return',
	'rol',
	'ror',
	'select',
	'severity',
	'signal',
	'shared',
	'sla',
	'sll',
	'sra',
	'srl',
	'subtype',
	'then',
	'to',
	'transport',
	'type',
	'unaffected',
	'units',
	'until',
	'use',
	'variable',
	'wait',
	'when',
	'while',
	'with',
	'xnor',
	'xor',
	# types from standard
	'bit',
	'bit_vector',
	'integer',
	'natural',
	'positive',
	'boolean',
	'string',
	'character',
	'real',
	'time',
	'delay_length',
	# types from std_logic_1164
	'std_ulogic',
	'std_ulogic_vector',
	'std_logic',
	'std_logic_vector',
	# types from numeric_std
	'signed',
	'unsigned',
	# types from text_io
	'line',
	'text',
	'side',
	'width',
		]

# These packages are not allowed to be used.
_PACKAGES_DEPRECATED = [
	"std_logic_arith",
	"std_logic_signed",
	"std_logic_unsigned"
	]

# These components are ignored for direct instantiation checks.
# This will generally be things that must always use component declaration.
_COMPONENTS_IGNORED = [
	"axis_register_slice_v1_1_15_axis_register_slice",
	"axis_dwidth_converter_v1_1_14_axis_dwidth_converter",
	"axis_clock_converter_v1_1_20_axis_clock_converter",
	"iobuf",
	]


class _LintState(object):
	"""Maintains module-wide state.."""

	def __init__(self):
		self.verbose_level = 1  # global setting.
		self.error_count = 0  # global count of reported errors
		# filters to apply when emitting error messages
		self.filters = _DEFAULT_FILTERS[:]
		# backup of filter list. Used to restore the state after each file.
		self._filters_backup = self.filters[:]
		self.counting = 'total'  # In what way are we counting errors?
		self.errors_by_category = {}  # string to int dict storing error counts
		self.quiet = False  # Suppress non-error messagess?

		# output format:
		# "emacs" - format that emacs can parse (default)
		# "eclipse" - format that eclipse can parse
		# "vs7" - format that Microsoft Visual Studio 7 can parse
		# "junit" - format that Jenkins, Bamboo, etc can parse
		# "sed" - returns a gnu sed command to fix the problem
		# "gsed" - like sed, but names the command gsed, e.g. for macOS homebrew users
		self.output_format = 'emacs'

		# For JUnit output, save errors and failures until the end so that they
		# can be written into the XML
		self._junit_errors = []
		self._junit_failures = []

	def SetOutputFormat(self, output_format):
		"""Sets the output format for errors."""
		self.output_format = output_format

	def SetQuiet(self, quiet):
		"""Sets the module's quiet settings, and returns the previous setting."""
		last_quiet = self.quiet
		self.quiet = quiet
		return last_quiet

	def SetVerboseLevel(self, level):
		"""Sets the module's verbosity, and returns the previous setting."""
		last_verbose_level = self.verbose_level
		self.verbose_level = level
		return last_verbose_level

	def SetCountingStyle(self, counting_style):
		"""Sets the module's counting options."""
		self.counting = counting_style

	def SetFilters(self, filters):
		"""Sets the error-message filters.
		These filters are applied when deciding whether to emit a given
		error message.
		Args:
			filters: A string of comma-separated filters (eg "+whitespace/indent").
							 Each filter should start with + or -; else we die.
		Raises:
			ValueError: The comma-separated filters did not all start with '+' or '-'.
									E.g. "-,+whitespace,-whitespace/indent,whitespace/badfilter"
		"""
		# Default filters always have less priority than the flag ones.
		self.filters = _DEFAULT_FILTERS[:]
		self.AddFilters(filters)

	def AddFilters(self, filters):
		""" Adds more filters to the existing list of error-message filters. """
		for filt in filters.split(','):
			clean_filt = filt.strip()
			if clean_filt:
				self.filters.append(clean_filt)
		for filt in self.filters:
			if not (filt.startswith('+') or filt.startswith('-')):
				raise ValueError('Every filter in --filters must start with + or -'
												 ' (%s does not)' % filt)

	def BackupFilters(self):
		""" Saves the current filter list to backup storage."""
		self._filters_backup = self.filters[:]

	def RestoreFilters(self):
		""" Restores filters previously backed up."""
		self.filters = self._filters_backup[:]

	def ResetErrorCounts(self):
		"""Sets the module's error statistic back to zero."""
		self.error_count = 0
		self.errors_by_category = {}

	def IncrementErrorCount(self, category):
		"""Bumps the module's error statistic."""
		self.error_count += 1
		if self.counting in ('toplevel', 'detailed'):
			if self.counting != 'detailed':
				category = category.split('/')[0]
			if category not in self.errors_by_category:
				self.errors_by_category[category] = 0
			self.errors_by_category[category] += 1

	def PrintErrorCounts(self):
		"""Print a summary of errors by category, and the total."""
		for category, count in sorted(iteritems(self.errors_by_category)):
			self.PrintInfo('Category \'%s\' errors found: %d\n' %
											 (category, count))
		if self.error_count > 0:
			self.PrintInfo('Total errors found: %d\n' % self.error_count)

	def PrintInfo(self, message):
		# _quiet does not represent --quiet flag.
		# Hide infos from stdout to keep stdout pure for machine consumption
		if not _quiet and self.output_format not in _MACHINE_OUTPUTS:
			sys.stdout.write(message)

	def PrintError(self, message):
		if self.output_format == 'junit':
			self._junit_errors.append(message)
		else:
			sys.stderr.write(message)

	def PrintVerbose(self, message):
		if not _quiet and  _lint_state.verbose_level == 0:
			sys.stdout.write(message)

	def AddJUnitFailure(self, filename, linenum, message, category, confidence):
		self._junit_failures.append((filename, linenum, message, category,
				confidence))

	def FormatJUnitXML(self):
		num_errors = len(self._junit_errors)
		num_failures = len(self._junit_failures)

		testsuite = xml.etree.ElementTree.Element('testsuite')
		testsuite.attrib['errors'] = str(num_errors)
		testsuite.attrib['failures'] = str(num_failures)
		testsuite.attrib['name'] = 'vhdllint'

		if num_errors == 0 and num_failures == 0:
			testsuite.attrib['tests'] = str(1)
			xml.etree.ElementTree.SubElement(testsuite, 'testcase', name='passed')

		else:
			testsuite.attrib['tests'] = str(num_errors + num_failures)
			if num_errors > 0:
				testcase = xml.etree.ElementTree.SubElement(testsuite, 'testcase')
				testcase.attrib['name'] = 'errors'
				error = xml.etree.ElementTree.SubElement(testcase, 'error')
				error.text = '\n'.join(self._junit_errors)
			if num_failures > 0:
				# Group failures by file
				failed_file_order = []
				failures_by_file = {}
				for failure in self._junit_failures:
					failed_file = failure[0]
					if failed_file not in failed_file_order:
						failed_file_order.append(failed_file)
						failures_by_file[failed_file] = []
					failures_by_file[failed_file].append(failure)
				# Create a testcase for each file
				for failed_file in failed_file_order:
					failures = failures_by_file[failed_file]
					testcase = xml.etree.ElementTree.SubElement(testsuite, 'testcase')
					testcase.attrib['name'] = failed_file
					failure = xml.etree.ElementTree.SubElement(testcase, 'failure')
					template = '{0}: {1} [{2}] [{3}]'
					texts = [template.format(f[1], f[2], f[3], f[4]) for f in failures]
					failure.text = '\n'.join(texts)

		xml_decl = '<?xml version="1.0" encoding="UTF-8" ?>\n'
		return xml_decl + xml.etree.ElementTree.tostring(testsuite, 'utf-8').decode('utf-8')


_lint_state = _LintState()


def _OutputFormat():
	"""Gets the module's output format."""
	return _lint_state.output_format


def _SetOutputFormat(output_format):
	"""Sets the module's output format."""
	_lint_state.SetOutputFormat(output_format)


def _Quiet():
	"""Return's the module's quiet setting."""
	return _lint_state.quiet


def _SetQuiet(quiet):
	"""Set the module's quiet status, and return previous setting."""
	return _lint_state.SetQuiet(quiet)


def _VerboseLevel():
	"""Returns the module's verbosity setting."""
	return _lint_state.verbose_level


def _SetVerboseLevel(level):
	"""Sets the module's verbosity, and returns the previous setting."""
	return _lint_state.SetVerboseLevel(level)


def _SetCountingStyle(level):
	"""Sets the module's counting options."""
	_lint_state.SetCountingStyle(level)


def _Filters():
	"""Returns the module's list of output filters, as a list."""
	return _lint_state.filters


def _SetFilters(filters):
	"""Sets the module's error-message filters.
	These filters are applied when deciding whether to emit a given
	error message.
	Args:
		filters: A string of comma-separated filters (eg "whitespace/indent").
						 Each filter should start with + or -; else we die.
	"""
	_lint_state.SetFilters(filters)


def _AddFilters(filters):
	"""Adds more filter overrides.
	Unlike _SetFilters, this function does not reset the current list of filters
	available.
	Args:
		filters: A string of comma-separated filters (eg "whitespace/indent").
						 Each filter should start with + or -; else we die.
	"""
	_lint_state.AddFilters(filters)


def _BackupFilters():
	""" Saves the current filter list to backup storage."""
	_lint_state.BackupFilters()


def _RestoreFilters():
	""" Restores filters previously backed up."""
	_lint_state.RestoreFilters()


def PrintUsage(message):
	"""Prints a brief usage string and exits, optionally with an error message.
	Args:
		message: The optional error message.
	"""
	sys.stderr.write(_USAGE	 % (list(GetAllExtensions()),
			 ','.join(list(GetAllExtensions()))))

	if message:
		sys.exit('\nFATAL ERROR: ' + message)
	else:
		sys.exit(0)


def PrintVersion():
	sys.stdout.write('vhdllint ' + __VERSION__ + '\n')
	sys.stdout.write('Python ' + sys.version + '\n')
	sys.exit(0)


def PrintCategories():
	"""Prints a list of all the error-categories used by error messages.
	These are the categories used to filter messages via --filter.
	"""
	sys.stderr.write(''.join('	%s\n' % cat for cat in _ERROR_CATEGORIES))
	sys.exit(0)


def _ShouldPrintError(category, confidence, linenum):
	"""If confidence >= verbose, category passes filter and is not suppressed."""

	# There are three ways we might decide not to print an error message:
	# a "NOLINT(category)" comment appears in the source,
	# the verbosity level isn't high enough, or the filters filter it out.
	if IsErrorSuppressedByNolint(category, linenum):
		return False

	if confidence < _lint_state.verbose_level:
		return False

	is_filtered = False
	for one_filter in _Filters():
		if one_filter.startswith('-'):
			if category.startswith(one_filter[1:]):
				is_filtered = True
		elif one_filter.startswith('+'):
			if category.startswith(one_filter[1:]):
				is_filtered = False
		else:
			assert False  # should have been checked for in SetFilter.
	if is_filtered:
		return False

	return True


def Error(filename, lineref, category, confidence, message):
	"""Logs the fact we've found a lint error.
	We log where the error was found, and also our confidence in the error,
	that is, how certain we are this is a legitimate style regression, and
	not a misidentification or a use that's sometimes justified.
	False positives can be suppressed by the use of
	"NOLINT(category)"	comments on the offending line.	These are
	parsed into _error_suppressions.
	Args:
		filename: The name of the file containing the error.
		lineref: The reference of the line containing the error.
		category: A string used to describe the "category" this bug
			falls under: "whitespace", say, or "runtime".	Categories
			may have a hierarchy separated by slashes: "whitespace/indent".
		confidence: A number from 1-5 representing a confidence score for
			the error, with 5 meaning that we are certain of the problem,
			and 1 meaning that it could be a legitimate construct.
		message: The error message.
	"""
	linenum = lineref.Line()

	if _ShouldPrintError(category, confidence, linenum):
		_lint_state.IncrementErrorCount(category)
		if _lint_state.output_format == 'vs7':
			_lint_state.PrintError('%s(%s): error vhdllint: [%s] %s [%d]\n' % (
					filename, linenum, category, message, confidence))
		elif _lint_state.output_format == 'eclipse':
			sys.stderr.write('%s:%s: warning: %s	[%s] [%d]\n' % (
					filename, linenum, message, category, confidence))
		elif _lint_state.output_format == 'junit':
			_lint_state.AddJUnitFailure(filename, linenum, message, category,
					confidence)
		elif _lint_state.output_format in ['sed', 'gsed']:
			if message in _SED_FIXUPS:
				sys.stdout.write(_lint_state.output_format + " -i '%s%s' %s # %s	[%s] [%d]\n" % (
						linenum, _SED_FIXUPS[message], filename, message, category, confidence))
			else:
				sys.stderr.write('# %s:%s:	"%s"	[%s] [%d]\n' % (
						filename, linenum, message, category, confidence))
		else:
			final_message = '%s:%s:[%d,%d]:	%s	[%s] [%d]\n' % (filename, linenum, lineref.Column()+1, lineref.EndColumn()+1, message, category, confidence)
			sys.stderr.write(final_message)


# The allowed extensions for file names
# This is set by --extensions flag
def GetAllExtensions():
	return _valid_extensions or set(['vhd', 'vhdl'])


def ProcessExtensionsOption(val):
	global _valid_extensions
	try:
		extensions = [ext.strip() for ext in val.split(',')]
		_valid_extensions = set(extensions)
	except ValueError:
		PrintUsage('Extensions should be a comma-separated list of values;'
							 'for example: extensions=vhd,vhdl\n'
							 'This could not be parsed: "%s"' % (val,))


def ParseNolintSuppressions(filename, raw_line, linenum, error):
	"""Updates the global list of line error-suppressions.
	Parses any NOLINT comments on the current line, updating the global
	error_suppressions store.	Reports an error if the NOLINT comment
	was malformed.
	Args:
		filename: str, the name of the input file.
		raw_line: str, the line of input text, with comments.
		linenum: int, the number of the current line.
		error: function, an error handler.
	"""
	matched = Search(r'\bNOLINT(NEXTLINE|BEGIN|END)?\b(\([^)]+\))?', raw_line)
	if matched:
		if matched.group(1) == "NEXTLINE":
			suppressed_line = linenum + 1
		else:
			suppressed_line = linenum

		begin_region = matched.group(1) == "BEGIN"
		end_region = matched.group(1) == "END"

		category = matched.group(2)
		if category in (None, '(*)'):  # => "suppress all"
			_error_suppressions.setdefault(None, set()).add(suppressed_line)
		else:
			if category.startswith('(') and category.endswith(')'):
				category = category[1:-1]
				if category in _ERROR_CATEGORIES:
					if begin_region:
						_error_suppressions_region.add(category)
					elif end_region:
						if category in _error_suppressions_region:
							_error_suppressions_region.remove(category)

					_error_suppressions.setdefault(category, set()).add(suppressed_line)
				else:
					error(filename, LineRef.FromString(linenum, raw_line, category), 'readability/nolint', 5, 'Unknown NOLINT error category: %s' % category)

	# handle suppressed regions
	for category in _error_suppressions_region:
		_error_suppressions.setdefault(category, set()).add(linenum)


def ProcessGlobalSuppresions(lines):
	"""Updates the list of global error suppressions.
	Parses any lint directives in the file that have global effect.
	Args:
		lines: An array of strings, each representing a line of the file, with the
					 last element being empty if the file is terminated with a newline.
	"""
	return False


def ResetNolintSuppressions():
	"""Resets the set of NOLINT suppressions to empty."""
	_error_suppressions.clear()
	_error_suppressions_region.clear()
	_global_error_suppressions.clear()


def ResetFileData():
	"""Resets data used while processing a single file."""
	_signal_identifiers.clear()
	_constant_identifiers.clear()
	_local_identifiers.clear()
	_other_identifiers.clear()
	_all_identifiers.clear()
	_drivers.clear()

class LineRef(object):
	"""Track a identifier line reference and column region"""

	def __init__(self, line, column, end_column=None, length=1):
		self.line = line  # line declared on
		self.column = column # starting column
		if end_column is None:
			self.end_column = column + length
		else:
			self.end_column = end_column # ending column

	def Line(self):
		"""Return the line number of the reference"""
		return self.line

	def Column(self):
		"""Return the starting column number of the reference"""
		return self.column

	def EndColumn(self):
		"""Return the ending column number of the reference"""
		return self.end_column

	@classmethod
	def FromString(cls, line_num, line, name, use_word_boundary=True):
		if use_word_boundary:
			match = re.search(r'\b(%s)\b' % re.escape(name), line)
		else:
			match = re.search(r'(%s)' % re.escape(name), line)
		pos = match.start() if match else 0
		return cls(line_num, pos, length=len(name))


	@classmethod
	def FromStringR(cls, line_num, line, name):
		match = re.search(r'(?s:.*)\b(%s)\b' % re.escape(name), line)
		pos = match.start(1) if match else 0
		return cls(line_num, pos, length=len(name))

	@classmethod
	def OnlyLine(cls, line_num):
		return cls(line_num, 0, 1)

class Identifier(object):

	def __init__(self, name, lineref):
		self.name = name
		self.lineref = lineref
		self.refs = 0  # references

	def Name(self):
		return self.name

	def Line(self):
		return self.lineref.Line()

	def Column(self):
		return self.lineref.Column()

	def EndColumn(self):
		return self.lineref.EndColumn()

	def IsReferenced(self):
		return self.refs > 0

	def IncRefs(self):
		self.refs += 1

	def Refs(self):
		return self.refs

class ReferencedIdentifier(Identifier):
	pass

class IdentifierWithType(ReferencedIdentifier):

	def __init__(self, name, stype, init, lineref):
		super().__init__(name, lineref)
		self.stype = stype  # data type
		self.init = init  # initialization
		self.drivers = []  # locations where this is driven (written)

	# check if type is boolean
	def IsBoolean(self):
		return self.stype.lower() == 'boolean'

	# check if there is an init value
	def HasInitValue(self):
		return self.init is not None

	def AddDriver(self, d):
		self.drivers.append(d)

	def GetDrivers(self):
		return self.drivers

	def GetUniqueDrivers(self):
		return set(self.drivers)

	def GetNumDrivers(self):
		return len(self.GetDrivers())

	def GetNumUniqueDrivers(self):
		return len(self.GetUniqueDrivers())

	def HasMultipleDrivers(self):
		unique = self.GetUniqueDrivers()
		# remove all unsure drivers
		# these are places that we don't know for sure are driving
		known = set([i for i in unique if not isinstance(i, PossibleDriver)])
		return len(known) > 1


class Driver(object):

	def __init__(self, scope, line):
		self.scope = scope  # scope name or other identifier
		self.line = line  # line where the driver is located

	# two drivers on the same line are treated as the same
	def __eq__(self, other):
		return self.line == other.line

	def __hash__(self):
		return hash(self.line)


class PossibleDriver(Driver):
	pass


class ProcessDriver(Driver):

	# two drivers in the same process are treated as the same
	def __eq__(self, other):
		return self.scope == other.scope

	def __hash__(self):
		return hash(self.scope)


class Signal(IdentifierWithType):
	pass


class Constant(IdentifierWithType):
	pass

class LocalIdentifier(IdentifierWithType):
	pass

class Variable(LocalIdentifier):
	pass

class LocalConstant(LocalIdentifier):
	pass

class Port(Signal):

	def __init__(self, name, stype, init, mode, lineref):
		super().__init__(name, stype, init, lineref)
		self.mode = mode  # port mode, direction


def AddSignalIdentifier(name, stype, init, lineref, filename, error):
	s = Signal(name, stype, init, lineref)
	_signal_identifiers[name.lower()] = s
	_all_identifiers[name.lower()] = s
	if not name.islower():
		error(filename, lineref, 'readability/identifiers', 1, 'Invalid capitalization on \'%s\'. Non-constant identifiers should use all lower case.' % name)


def AddConstantIdentifier(name, stype, init, lineref):
	c = Constant(name, stype, init, lineref)
	_constant_identifiers[name.lower()] = c
	_all_identifiers[name.lower()] = c


def AddOtherIdentifier(name, lineref, filename, error):
	i = Identifier(name, lineref)
	_other_identifiers[name.lower()] = i
	_all_identifiers[name.lower()] = i
	if not name.islower():
		error(filename, lineref, 'readability/identifiers', 1, 'Invalid capitalization on \'%s\'. Non-constant identifiers should use all lower case.' % name)


def AddReferencedIdentifier(name, lineref, filename, error, enforce_caps=True):
	i = ReferencedIdentifier(name, lineref)
	_other_identifiers[name.lower()] = i
	_all_identifiers[name.lower()] = i
	if enforce_caps and not name.islower():
		error(filename, lineref, 'readability/identifiers', 1, 'Invalid capitalization on \'%s\'. Non-constant identifiers should use all lower case.' % name)


def AddPortIdentifier(name, stype, init, mode, lineref, filename, error):
	s = Port(name, stype, init, mode, lineref)
	_signal_identifiers[name.lower()] = s
	_all_identifiers[name.lower()] = s
	if not name.islower():
		error(filename, lineref, 'readability/identifiers', 1, 'Invalid capitalization on \'%s\'. Non-constant identifiers should use all lower case.' % name)


def IsReservedWord(name):
	return name.lower() in _VHDL_RESERVED


def IsSignalIdentifier(name):
	return name.lower() in _signal_identifiers


def GetSignalIdentifier(name):
	if name.lower() in _signal_identifiers:
		return _signal_identifiers[name.lower()]

	return None


def IsConstantIdentifier(name):
	return name.lower() in _constant_identifiers


def GetConstantIdentifier(name):
	if name.lower() in _constant_identifiers:
		return _constant_identifiers[name.lower()]

	return None


def IsVariableIdentifier(name):
	for scope in _local_identifiers:
		if name.lower() in scope:
			return not isinstance(scope[name.lower()], LocalConstant)

	return False


def GetVariableIdentifier(name):
	for scope in _local_identifiers:
		if name.lower() in scope:
			return scope[name.lower()]

	return None


def IsOtherIdentifier(name):
	return name.lower() in _other_identifiers


def IsIdentifier(name):
	return name.lower() in _all_identifiers


def GetIdentifier(name):
	if name.lower() in _all_identifiers:
		return _all_identifiers[name.lower()]

	return None


def IsSignalOrVariableIdentifier(name):
	return IsVariableIdentifier(name) or IsSignalIdentifier(name)


def IsIdentifierWithType(name):
	# check locals
	if IsVariableIdentifier(name):
		return True

	if IsSignalIdentifier(name):
		return True

	if IsConstantIdentifier(name):
		return True

	return False


def IsReferencedIdentifier(name):
	if not IsIdentifier(name):
		return False
	if not isinstance(GetIdentifier(name), ReferencedIdentifier):
		return False

	return True


def GetIdentifierWithType(name):
	# check locals
	if IsVariableIdentifier(name):
		return GetVariableIdentifier(name)

	if IsSignalIdentifier(name):
		return GetSignalIdentifier(name)

	if IsConstantIdentifier(name):
		return GetConstantIdentifier(name)

	return None


# start a new scope for locals
def AddLocalScope():
	# add empty map
	_local_identifiers.append({})


# remove all locals in the current scope
def RemoveLocalScope(filename, error):

	# check items in current scope
	for i in GetAllLocalIdentifiers():
		if not i.IsReferenced():
			error(filename, i.lineref, 'build/unused', 2, 'Unused local identifier \'%s\'.' % (i.Name()))

		# remove local
		if i.Name().lower() in _all_identifiers:
			if _all_identifiers[i.Name().lower()] == i:
				_all_identifiers.pop(i.Name().lower(), None)

	# remove last element
	_local_identifiers.pop()


# add local identifier to current scope
def AddLocalIdentifier(name, stype, init, lineref, filename, error, is_constant=False):
	if is_constant:
		v = LocalConstant(name, stype, init, lineref)
	else:
		v = Variable(name, stype, init, lineref)
		if not name.islower():
			error(filename, lineref, 'readability/identifiers', 1, 'Invalid capitalization on \'%s\'. Non-constant identifiers should use all lower case.' % name)

	_local_identifiers[-1][name.lower()] = v
	_all_identifiers[name.lower()] = v


def GetAllLocalIdentifiers():
	return _local_identifiers[-1].values()


def IsErrorSuppressedByNolint(category, linenum):
	"""Returns true if the specified error category is suppressed on this line.
	Consults the global error_suppressions map populated by
	ParseNolintSuppressions/ProcessGlobalSuppresions/ResetNolintSuppressions.
	Args:
	  category: str, the category of the error.
	  linenum: int, the current line number.
	Returns:
	  bool, True iff the error should be suppressed due to a NOLINT comment or
	  global suppression.
	"""
	return (_global_error_suppressions.get(category, False) or
	        linenum in _error_suppressions.get(category, set()) or
	        linenum in _error_suppressions.get(None, set()))


def FindNextMultiLineCommentStart(lines, lineix):
	"""Find the beginning marker for a multiline comment."""
	while lineix < len(lines):
		if lines[lineix].strip().startswith('/*'):
			# Only return this marker if the comment goes beyond this line
			if lines[lineix].strip().find('*/', 2) < 0:
				return lineix
		lineix += 1
	return len(lines)


def FindNextMultiLineCommentEnd(lines, lineix):
	"""We are inside a comment, find the end marker."""
	while lineix < len(lines):
		if lines[lineix].strip().endswith('*/'):
			return lineix
		lineix += 1
	return len(lines)


def RemoveMultiLineCommentsFromRange(lines, begin, end):
	"""Clears a range of lines for multi-line comments."""
	# Having // <empty> comments makes the lines non-empty, so we will not get
	# unnecessary blank line warnings later in the code.
	for i in range(begin, end):
		lines[i] = '/**/'


def RemoveMultiLineComments(filename, lines, error):
	"""Removes multiline (c-style) comments from lines."""
	lineix = 0
	while lineix < len(lines):
		lineix_begin = FindNextMultiLineCommentStart(lines, lineix)
		if lineix_begin >= len(lines):
			return
		lineix_end = FindNextMultiLineCommentEnd(lines, lineix_begin)
		if lineix_end >= len(lines):
			error(filename, LineRef.OnlyLine(lineix_begin + 1), 'readability/multiline_comment', 5,
				'Could not find end of multi-line comment')
			return
		RemoveMultiLineCommentsFromRange(lines, lineix_begin, lineix_end + 1)
		lineix = lineix_end + 1


def IsCppString(line):
	"""Does line terminate so, that the next symbol is in string constant.
	This function does not consider single-line nor multi-line comments.
	Args:
		line: is a partial line of code starting from the 0..n.
	Returns:
		True, if next character appended to 'line' is inside a
		string constant.
	"""

	line = line.replace(r'--', 'XX')  # after this, \\" does not match to \"
	return ((line.count('"') - line.count(r'\"') - line.count("'\"'")) & 1) == 1


def CleanseComments(line):
	"""Removes //-comments and single-line C-style /* */ comments.
	Args:
		line: A line of C++ source.
	Returns:
		The line with single-line comments removed.
	"""
	commentpos = line.find('--')
	if commentpos != -1 and not IsCppString(line[:commentpos]):
		line = line[:commentpos].rstrip()
	# get rid of /* ... */
	return _RE_PATTERN_CLEANSE_LINE_C_COMMENTS.sub('', line)


_RE_PATTERN_INCLUDE = re.compile(r'^\s*#\s*include\s*([<"])([^>"]*)[>"].*$')
# Matches standard C++ escape sequences per 2.13.2.3 of the C++ standard.
_RE_PATTERN_CLEANSE_LINE_ESCAPES = re.compile(
	  r'\\([abfnrtv?"\\\']|\d+|x[0-9a-fA-F]+)')
# Match a single C style comment on the same line.
_RE_PATTERN_C_COMMENTS = r'/\*(?:[^*]|\*(?!/))*\*/'
# Matches multi-line C style comments.
# This RE is a little bit more complicated than one might expect, because we
# have to take care of space removals tools so we can handle comments inside
# statements better.
# The current rule is: We only clear spaces from both sides when we're at the
# end of the line. Otherwise, we try to remove spaces from the right side,
# if this doesn't work we try on left side but only if there's a non-character
# on the right.
_RE_PATTERN_CLEANSE_LINE_C_COMMENTS = re.compile(
	  r'(\s*' + _RE_PATTERN_C_COMMENTS + r'\s*$|' +
	  _RE_PATTERN_C_COMMENTS + r'\s+|' +
	  r'\s+' + _RE_PATTERN_C_COMMENTS + r'(?=\W)|' +
	  _RE_PATTERN_C_COMMENTS + r')')

# possible identifier uses
# abc, abc(0), abc.xyz(0)
_PATTERN_IDENTIFIER_USE = r'((\w[\w\.]*)(\s*\(.*?\))?)'


def Match(pattern, s):
	"""Matches the string with the pattern, caching the compiled regexp."""
	# The regexp compilation caching is inlined in both Match and Search for
	# performance reasons; factoring it out into a separate function turns out
	# to be noticeably expensive.
	if pattern not in _regexp_compile_cache:
		_regexp_compile_cache[pattern] = sre_compile.compile(pattern, sre_compile.SRE_FLAG_IGNORECASE)
	return _regexp_compile_cache[pattern].match(s)


def Search(pattern, s):
	"""Searches the string for the pattern, caching the compiled regexp."""
	if pattern not in _regexp_compile_cache:
		_regexp_compile_cache[pattern] = sre_compile.compile(pattern)
	return _regexp_compile_cache[pattern].search(s)


class CleansedLines(object):
	"""Holds 4 copies of all lines with different preprocessing applied to them.
	1) elided member contains lines without strings and comments.
	2) lines member contains lines without comments.
	3) raw_lines member contains all the lines without processing.
	4) lines_without_raw_strings member is same as raw_lines, but with C++11 raw
		 strings removed.
	All these members are of <type 'list'>, and of the same length.
	"""

	def __init__(self, lines):
		self.elided = []
		self.lines = []
		self.raw_lines = lines
		self.num_lines = len(lines)
		# self.lines_without_raw_strings = CleanseRawStrings(lines)
		for linenum in range(len(self.raw_lines)):
			self.lines.append(CleanseComments(self.raw_lines[linenum]))
			elided = self._CollapseStrings(self.lines[linenum])
			self.elided.append(CleanseComments(elided))

	def NumLines(self):
		"""Returns the number of lines represented."""
		return self.num_lines

	@staticmethod
	def _CollapseStrings(elided):
		"""Collapses strings and chars on a line to simple "" or '' blocks.
		We nix strings first so we're not fooled by text like '"http://"'
		Args:
			elided: The line being processed.
		Returns:
			The line with collapsed strings.
		"""
		if _RE_PATTERN_INCLUDE.match(elided):
			return elided

		# Remove escaped characters first to make quote/single quote collapsing
		# basic.	Things that look like escaped characters shouldn't occur
		# outside of strings and chars.
		elided = _RE_PATTERN_CLEANSE_LINE_ESCAPES.sub('', elided)

		# Replace quoted strings and digit separators.	Both single quotes
		# and double quotes are processed in the same loop, otherwise
		# nested quotes wouldn't work.
		collapsed = ''
		while True:
			# Find the first quote character
			match = Match(r'^([^\'"]*)([\'"])(.*)$', elided)
			if not match:
				collapsed += elided
				break
			head, quote, tail = match.groups()

			if quote == '"':
				# Collapse double quoted strings
				second_quote = tail.find('"')
				if second_quote >= 0:
					collapsed += head + '""'
					elided = tail[second_quote + 1:]
				else:
					# Unmatched double quote, don't bother processing the rest
					# of the line since this is probably a multiline string.
					collapsed += elided
					break
			else:
				collapsed += elided
				break
				# Found single quote, check nearby text to eliminate digit separators.
				#
				# There is no special handling for floating point here, because
				# the integer/fractional/exponent parts would all be parsed
				# correctly as long as there are digits on both sides of the
				# separator.	So we are fine as long as we don't see something
				# like "0.'3" (gcc 4.9.0 will not allow this literal).
# 				if Search(r'\b(?:0[bBxX]?|[1-9])[0-9a-fA-F]*$', head):
# 					match_literal = Match(r'^((?:\'?[0-9a-zA-Z_])*)(.*)$', "'" + tail)
# 					collapsed += head + match_literal.group(1).replace("'", '')
# 					elided = match_literal.group(2)
# 				else:
# 					second_quote = tail.find('\'')
# 					if second_quote >= 0:
# 						collapsed += head + "''"
# 						elided = tail[second_quote + 1:]
# 					else:
# 						# Unmatched single quote
# 						collapsed += elided
# 						break

		return collapsed


def FindEndOfExpressionInLine(line, startpos, stack):
	"""Find the position just after the end of current parenthesized expression.
	Args:
		line: a CleansedLines line.
		startpos: start searching at this position.
		stack: nesting stack at startpos.
	Returns:
		On finding matching end: (index just after matching end, None)
		On finding an unclosed expression: (-1, None)
		Otherwise: (-1, new stack at end of this line)
	"""
	for i in xrange(startpos, len(line)):
		char = line[i]
		if char in '([{':
			# Found start of parenthesized expression, push to expression stack
			stack.append(char)
		elif char == '<':
			# Found potential start of template argument list
			if i > 0 and line[i - 1] == '<':
				# Left shift operator
				if stack and stack[-1] == '<':
					stack.pop()
					if not stack:
						return (-1, None)
			elif i > 0 and Search(r'\boperator\s*$', line[0:i]):
				# operator<, don't add to stack
				continue
			else:
				# Tentative start of template argument list
				stack.append('<')
		elif char in ')]}':
			# Found end of parenthesized expression.
			#
			# If we are currently expecting a matching '>', the pending '<'
			# must have been an operator.	Remove them from expression stack.
			while stack and stack[-1] == '<':
				stack.pop()
			if not stack:
				return (-1, None)
			if ((stack[-1] == '(' and char == ')') or
					(stack[-1] == '[' and char == ']') or
					(stack[-1] == '{' and char == '}')):
				stack.pop()
				if not stack:
					return (i + 1, None)
			else:
				# Mismatched parentheses
				return (-1, None)
		elif char == '>':
			# Found potential end of template argument list.

			# Ignore "->" and operator functions
			if (i > 0 and
					(line[i - 1] == '-' or Search(r'\boperator\s*$', line[0:i - 1]))):
				continue

			# Pop the stack if there is a matching '<'.	Otherwise, ignore
			# this '>' since it must be an operator.
			if stack:
				if stack[-1] == '<':
					stack.pop()
					if not stack:
						return (i + 1, None)
		elif char == ';':
			# Found something that look like end of statements.	If we are currently
			# expecting a '>', the matching '<' must have been an operator, since
			# template argument list should not contain statements.
			while stack and stack[-1] == '<':
				stack.pop()
			if not stack:
				return (-1, None)

	# Did not find end of expression or unbalanced parentheses on this line
	return (-1, stack)


def CloseExpression(clean_lines, linenum, pos):
	"""If input points to ( or { or [ or <, finds the position that closes it.
	If lines[linenum][pos] points to a '(' or '{' or '[' or '<', finds the
	linenum/pos that correspond to the closing of the expression.
	TODO(unknown): vhdllint spends a fair bit of time matching parentheses.
	Ideally we would want to index all opening and closing parentheses once
	and have CloseExpression be just a simple lookup, but due to preprocessor
	tricks, this is not so easy.
	Args:
		clean_lines: A CleansedLines instance containing the file.
		linenum: The number of the line to check.
		pos: A position on the line.
	Returns:
		A tuple (line, linenum, pos) pointer *past* the closing brace, or
		(line, len(lines), -1) if we never find a close.	Note we ignore
		strings and comments when matching; and the line we return is the
		'cleansed' line at linenum.
	"""

	line = clean_lines.elided[linenum]
	if (line[pos] not in '({[<') or Match(r'<[<=]', line[pos:]):
		return (line, clean_lines.NumLines(), -1)

	# Check first line
	(end_pos, stack) = FindEndOfExpressionInLine(line, pos, [])
	if end_pos > -1:
		return (line, linenum, end_pos)

	# Continue scanning forward
	while stack and linenum < clean_lines.NumLines() - 1:
		linenum += 1
		line = clean_lines.elided[linenum]
		(end_pos, stack) = FindEndOfExpressionInLine(line, 0, stack)
		if end_pos > -1:
			return (line, linenum, end_pos)

	# Did not find end of expression before end of file, give up
	return (line, clean_lines.NumLines(), -1)


def ExtractExpression(clean_lines, line_num, pos):
	(endline, endlinenum, endpos) = CloseExpression(clean_lines, line_num, pos)
	if line_num == endlinenum:
		return (clean_lines.lines[line_num][pos + 1:endpos - 1], endlinenum, endpos)

	string = clean_lines.lines[line_num][pos + 1:]
	for l in xrange(line_num + 1, endlinenum):
		string = string + clean_lines.lines[l]

	string = string + endline[:endpos - 1]
	return (string, endlinenum, endpos)


def CheckForCopyright(filename, lines, error):
	"""Logs an error if no Copyright message appears at the top of the file."""

	# We'll say it should occur by line 30. Don't forget there's a
	# placeholder line at the front.
	for line in xrange(1, min(len(lines), 31)):
		if Search(r'Copyright', lines[line]): break
	else:  # means no copyright line was found
		error(filename, LineRef.OnlyLine(0), 'legal/copyright', 5,
					'No copyright message found.  '
					'You should have a line: "Copyright [year] <Copyright Owner>"')


def CheckForHeader(filename, lines, error):
	"""Logs an error if no header comment appears at the top of the file."""

	if not lines[1].startswith('--'):
		error(filename, LineRef.OnlyLine(0), 'readability/header', 5, 'No file header found.')


def CheckForBadCharacters(filename, lines, error):
	"""Logs an error for each line containing bad characters.
	Two kinds of bad characters:
	1. Unicode replacement characters: These indicate that either the file
	contained invalid UTF-8 (likely) or Unicode replacement characters (which
	it shouldn't).	Note that it's possible for this to throw off line
	numbering if the invalid UTF-8 occurred adjacent to a newline.
	2. NUL bytes.	These are problematic for some tools.
	Args:
		filename: The name of the current file.
		lines: An array of strings, each representing a line of the file.
		error: The function to call with any errors found.
	"""
	for linenum, line in enumerate(lines):
		if unicode_escape_decode('\ufffd') in line:
			error(filename, LineRef.OnlyLine(linenum), 'readability/utf8', 5,
						'Line contains invalid UTF-8 (or Unicode replacement character).')
		if '\0' in line:
			error(filename, LineRef.FromString(linenum, line, '\0', use_word_boundary=False), 'readability/nul', 5, 'Line contains NUL byte.')


def CheckForNewlineAtEOF(filename, lines, error):
	"""Logs an error if there is no newline char at the end of the file.
	Args:
		filename: The name of the current file.
		lines: An array of strings, each representing a line of the file.
		error: The function to call with any errors found.
	"""

	# The array lines() was created by adding two newlines to the
	# original file (go figure), then splitting on \n.
	# To verify that the file ends in \n, we just have to make sure the
	# last-but-two element of lines() exists and is empty.
	if len(lines) < 3 or lines[-2]:
		error(filename, LineRef(len(lines) - 2, len( lines[-2])-1), 'whitespace/ending_newline', 5,
					'Could not find a newline character at the end of the file.')


def IsCommentLine(line):
	return Match(r'\s*--', line)


def IsBlankLine(line):
	return Match(r'\s*$', line)


def IsBlankOrCommentLine(line):
	return IsBlankLine(line) or IsCommentLine(line)


def IsPrevLineBlank(clean_lines, linenum):
	raw_lines = clean_lines.raw_lines
	line = raw_lines[linenum - 1] if linenum > 0 else ''
	return IsBlankLine(line)


def IsPrevLineBlankOrComment(clean_lines, linenum):
	raw_lines = clean_lines.raw_lines
	line = raw_lines[linenum - 1] if linenum > 0 else ''
	return IsBlankOrCommentLine(line)


def IsNextLineBlank(clean_lines, linenum):
	raw_lines = clean_lines.raw_lines
	line = raw_lines[linenum + 1] if linenum < clean_lines.NumLines() else ''
	return IsBlankLine(line)


def IsNextLineBlankOrComment(clean_lines, linenum):
	raw_lines = clean_lines.raw_lines
	line = raw_lines[linenum + 1] if linenum < clean_lines.NumLines() else ''
	return IsBlankOrCommentLine(line)


def CheckStyle(filename, clean_lines, linenum, file_extension, error):
	"""Checks rules from the 'C++ style rules' section of cppguide.html.
	Most of these rules are hard to test (naming, comment style), but we
	do what we can.	In particular we check for 2-space indents, line lengths,
	tab usage, spaces inside code, etc.
	Args:
		filename: The name of the current file.
		clean_lines: A CleansedLines instance containing the file.
		linenum: The number of the line to check.
		file_extension: The extension (without the dot) of the filename.
		nesting_state: A NestingState instance which maintains information about
									 the current stack of nested blocks being parsed.
		error: The function to call with any errors found.
	"""

	# Don't use "elided" lines here, otherwise we can't check commented lines.
	# Don't want to use "raw" either, because we don't want to check inside C++11
	# raw strings,
	raw_lines = clean_lines.raw_lines
	line = raw_lines[linenum]
	prev = raw_lines[linenum - 1] if linenum > 0 else ''

	if line.find('\t') != -1:
		error(filename, LineRef.FromString(linenum, line, '\t', use_word_boundary=False), 'whitespace/tab', 1, 'Tab found; better to use spaces')

	initial_spaces = 0
	while initial_spaces < len(line) and line[initial_spaces] == ' ':
		initial_spaces += 1

	# emacs will format function/procedures/type declarations on multiple lines with an odd number of spaces
	# try to detect that on the previous line by looking for 'XXXX('
	prev_is_call = Match(r'.*?\w+\s*\(', prev)
	prev_is_assign = Match(r'.*?<=.*?(?<!;)(?<!\bthen\b)$', prev) #.*?<=.*?(?<!;|then)$

	if initial_spaces % 2 != 0 and not prev_is_call and not prev_is_assign:
		# only report on first line of a group of lines
		prev_initial_spaces = 0
		while prev_initial_spaces < len(prev) and prev[prev_initial_spaces] == ' ':
			prev_initial_spaces += 1

		prev_is_same_spacing = prev_initial_spaces == initial_spaces
		if not prev_is_same_spacing:
			error(filename, LineRef(linenum, 0, initial_spaces), 'whitespace/indent', 3, 'Weird number of spaces at line-start. Are you using a 2-space indent?')

	if line and line[-1].isspace():
		error(filename, LineRef(linenum, len(line)-1), 'whitespace/end_of_line', 4, 'Line ends in whitespace.	Consider deleting these extra spaces.')

	# Check for multiple unnecessary blank lines
	blank_thresh = 3
	blank_cnt = 0
	for l in xrange(linenum, min(clean_lines.NumLines(), linenum + blank_thresh)):
		rline = raw_lines[l]
		if IsBlankLine(rline):
			blank_cnt = blank_cnt + 1
		if blank_cnt >= blank_thresh:
			error(filename, LineRef.OnlyLine(linenum), 'whitespace/blank_line', 4, 'Redundant blank lines. Consider deleting some of these extra lines.')
			break


def CheckUsedPackages(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]

	match = Match(r'\s*\blibrary\b\s+(.*?);', line)
	if match:
		libs = match.group(1)
		lib_list = "".join(libs.split()).split(",")  # remove whitespace before splitting
		for lib in lib_list:
			AddOtherIdentifier(lib, LineRef.FromString(line_num, line, lib), filename, error)
		# check used identifiers
		CheckIdentifiers(filename, clean_lines, line_num, error)

	# Check for non standard packages that should not be used
	match = Match(r'\s*\buse\b\s+(.*?);', line)
	if match:
		uses = match.group(1)
		use_list = "".join(uses.split()).split(",")  # remove whitespace before splitting
		for u in use_list:
			words = "".join(uses.split()).split(".")  # remove whitespace before splitting
			for w in words:
				if IsReservedWord(w):
					continue;
				AddOtherIdentifier(w, LineRef.FromString(line_num, line, w), filename, error)

				if w.lower() in _PACKAGES_DEPRECATED:
					error(filename, LineRef.FromString(line_num, line, w), 'build/deprecated', 5, 'Non-standard package \'%s\'. Use ieee.numeric_std instead.' % w)

		# check used identifiers
		CheckIdentifiers(filename, clean_lines, line_num, error)


_RE_PATTERN_TODO = re.compile(r'^--(\s*)TODO(\(.+?\))?:?(\s|$)?')


def CheckComment(line, filename, linenum, error):
	"""Checks for common mistakes in comments.
	Args:
		line: The line in question.
		filename: The name of the current file.
		linenum: The number of the line to check.
		error: The function to call with any errors found.
	"""
	commentpos = line.find('--')
	if commentpos != -1:
		# Check if the // may be in quotes.	If so, ignore it
		if re.sub(r'\\.', '', line[0:commentpos]).count('"') % 2 == 0:
			# Checks for common mistakes in TODO comments.
			comment = line[commentpos:]
			match = _RE_PATTERN_TODO.match(comment)
			if match:
				# One whitespace is correct; zero whitespace is handled elsewhere.
				leading_whitespace = match.group(1)
				wpos = commentpos+2
				wepos=wpos+len(leading_whitespace)
				if len(leading_whitespace) > 1:
					error(filename, LineRef(linenum, wpos, wepos), 'whitespace/todo', 2,
								'Too many spaces before TODO')

				username = match.group(2)
				if not username:
					error(filename, LineRef(linenum, wepos + 4), 'readability/todo', 2,
								'Missing username in TODO; it should look like '
								'"-- TODO(my_username): Stuff."', )

				middle_whitespace = match.group(3)
				# Comparisons made explicit for correctness -- pylint: disable=g-explicit-bool-comparison
				if middle_whitespace != ' ' and middle_whitespace != '':
					error(filename, LineRef(linenum,match.end(2) + 2), 'whitespace/todo', 2,
								'TODO(my_username) should be followed by a space', )

			# If the comment contains an alphanumeric character, there
			# should be a space somewhere between it and the -- unless
			# it's a --- comment.
			if (Match(r'--[^ ]*\w', comment) and not Match(r'(---)(\s+|$)', comment)):
				error(filename, LineRef(linenum, line.index("--") + 2), 'whitespace/comments', 4, 'Should have a space between -- and comment', )


def CheckFunction(filename, clean_lines, start_line, end_line, name, error, in_pkg=False):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected function \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddReferencedIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)
	AddLocalScope()

	# in a package we assume the identifier will be used externally
	if in_pkg:
		idt = GetIdentifier(name)
		idt.IncRefs()  # mark identifier as used

	# extract any params
	match = Search(r'\s*\bfunction\s+(\w+)\s*\(', line)
	el = start_line
	if match:
		# This could be a multiline
		pos = match.end() - 1
		(string, el, endpos) = ExtractExpression(clean_lines, start_line, pos)
		pos += 1  # skip open parenthesis
		endpos -= 1  # skip end parenthesis
		l = start_line
		while l <= el:
			ep = endpos if l == el else None  # use endpos on last line

			if l > start_line: # skip name
				# check used identifiers
				CheckIdentifiers(filename, clean_lines, l, error)

			match, decl_type, name_list, mode, stype, init, pos = MatchDeclaration(filename, clean_lines, l, error, pos, check_int_range=False, endpos=ep)
			if not match:
				l = l + 1
				continue

			# keep the same line to check again
			for name in name_list:
				_lint_state.PrintVerbose("Detected local \'%s\' : %s := %s on line %d\n" % (name, stype, init, l))
				AddLocalIdentifier(name, stype, init, LineRef.FromString(l, clean_lines.lines[l], name), filename, error)

	# check after params
	for l in xrange(el+1, end_line):
		line = clean_lines.lines[l]

		CheckBooleans(filename, clean_lines, l, error)

		# check used identifiers
		CheckIdentifiers(filename, clean_lines, l, error)

		# check variables, don't check integer ranges inside functions
		CheckVariables(filename, clean_lines, l, error, check_int_range=False)

		# check constants
		CheckLocalConstants(filename, clean_lines, l, error)

		CheckAsserts(filename, clean_lines, l, error)

	RemoveLocalScope(filename, error)


def CheckFunctions(filename, clean_lines, line_num, error, in_pkg=False):
	pline = clean_lines.lines[line_num]
	match = Match(r'\s*(\b(pure|impure)\s+)?\bfunction\s+(\w+)', pline)
	if not match:
		return False, 0

	start_line = line_num
	end_line = -1
	name = match.group(3)

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\b\s*(function|%s|function\s+%s|)\s*;' % (name, name), pline):
			end_line = l
			break
	if end_line < 0:
		return False, 0  # could not find end of function

	CheckFunction(filename, clean_lines, start_line, end_line, name, error, in_pkg=in_pkg)
	return True, end_line


def CheckFunctionDeclarations(filename, clean_lines, line_num, error):
	pline = clean_lines.lines[line_num]
	match = Match(r'\s*(\b(pure|impure)\s+)?\bfunction\s+(\w+)', pline)
	if not match:
		return False, 0

	start_line = line_num
	end_line = -1
	name = match.group(3)

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\breturn\b.*;', pline):
			end_line = l
			break
	if end_line < 0:
		return False, 0  # could not find end of function

	_lint_state.PrintVerbose("Detected function declaration \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddReferencedIdentifier(name, LineRef.FromString(start_line, clean_lines.lines[start_line], name), filename, error)

	# in a package we assume the identifier will be used externally
	idt = GetIdentifier(name)
	idt.IncRefs()  # mark identifier as used

	return True, end_line


def CheckRecord(filename, clean_lines, start_line, end_line, name, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected record \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddReferencedIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)

	for l in xrange(start_line, end_line):
		line = clean_lines.lines[l]

		# check used identifiers
		CheckIdentifiers(filename, clean_lines, l, error)

		match, decl_type, name_list, mode, stype, init, pos = MatchDeclaration(filename, clean_lines, l, error)
		if not match:
			continue

		for name in name_list:
			_lint_state.PrintVerbose("Detected record element declaration \'%s\' : %s\n" % (name, stype))


def CheckRecords(filename, clean_lines, line_num, error):
	pline = clean_lines.lines[line_num]
	match = Search(r'.*\btype\s+(\w+)\s+is\s+record\b', pline)
	if not match:
		return False, 0

	start_line = line_num
	end_line = -1
	name = match.group(1)

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\b\s*(record|record\s+%s|)\s*;' % (name), pline):
			end_line = l
			break
	if end_line < 0:
		return False, 0  # could not find end of function

	CheckRecord(filename, clean_lines, start_line, end_line, name, error)
	return True, end_line


def CheckProcedure(filename, clean_lines, start_line, end_line, name, error, in_pkg=False):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected procedure \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddReferencedIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)
	AddLocalScope()

	# in a package we assume the identifier will be used externally
	if in_pkg:
		idt = GetIdentifier(name)
		idt.IncRefs()  # mark identifier as used

	# extract any params
	match = Search(r'\s*\bprocedure\s+(\w+)\s*\(', line)
	el = start_line
	if match:
		# This could be a multiline
		pos = match.end() - 1
		(string, el, endpos) = ExtractExpression(clean_lines, start_line, pos)
		pos += 1  # skip open parenthesis
		endpos -= 1  # skip end parenthesis
		l = start_line
		while l <= el:
			ep = endpos if l == el else None  # use endpos on last line

			if l > start_line: # skip name
				# check used identifiers
				CheckIdentifiers(filename, clean_lines, l, error)

			match, decl_type, name_list, mode, stype, init, pos = MatchDeclaration(filename, clean_lines, l, error, pos, check_int_range=False, endpos=ep)
			if not match:
				l = l + 1
				continue

			# keep the same line to check again
			for name in name_list:
				_lint_state.PrintVerbose("Detected local \'%s\' : %s := %s on line %d\n" % (name, stype, init, l))
				AddLocalIdentifier(name, stype, init, LineRef.FromString(l, clean_lines.lines[l], name), filename, error)

	# check after params
	for l in xrange(el+1, end_line):
		line = clean_lines.lines[l]

		CheckBooleans(filename, clean_lines, l, error)

		# check used identifiers
		CheckIdentifiers(filename, clean_lines, l, error)

		# check variables, don't check integer ranges inside procedures
		CheckVariables(filename, clean_lines, l, error, check_int_range=False)

		# check constants
		CheckLocalConstants(filename, clean_lines, l, error)

		CheckAsserts(filename, clean_lines, l, error)

	RemoveLocalScope(filename, error)


def CheckProcedures(filename, clean_lines, line_num, error, in_pkg=False):
	pline = clean_lines.lines[line_num]
	match = Match(r'\s*\bprocedure\s+(\w+)', pline)
	if not match:
		return False, 0

	start_line = line_num
	end_line = -1
	name = match.group(1)

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\b\s*(procedure|%s|procedure\s+%s|)\s*;' % (name, name), pline):
			end_line = l
			break
	if end_line < 0:
		return False, 0  # could not find end of function

	CheckProcedure(filename, clean_lines, start_line, end_line, name, error, in_pkg=in_pkg)
	return True, end_line


def CheckProcedureDeclarations(filename, clean_lines, line_num, error):
	pline = clean_lines.lines[line_num]
	match = Search(r'\s*\bprocedure\s+(\w+)\s*\(', pline)
	if not match:
		return False, 0

	start_line = line_num
	end_line = -1
	name = match.group(1)

	# This could be a multiline
	pos = match.end() - 1
	(string, end_line, endpos) = ExtractExpression(clean_lines, line_num, pos)

	_lint_state.PrintVerbose("Detected procedure declaration \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddReferencedIdentifier(name, LineRef.FromString(start_line, pline, name), filename, error)

	# in a package we assume the identifier will be used externally
	idt = GetIdentifier(name)
	idt.IncRefs()  # mark identifier as used

	return True, end_line


def CheckComponent(filename, clean_lines, start_line, end_line, name, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected component \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	lineref = LineRef.FromString(start_line, line, name)
	AddReferencedIdentifier(name, lineref, filename, error)

	if name.lower() not in _COMPONENTS_IGNORED:
		error(filename, lineref, 'readability/components', 1, 'Detected component \'%s\'. Direct instantiation is preferred over component where possible.' % name)


def CheckComponents(filename, clean_lines, line_num, error):
	pline = clean_lines.lines[line_num]
	match = Match(r'\s*\bcomponent\s+(\w+)', pline)
	if not match:
		return False, 0

	start_line = line_num
	end_line = -1
	name = match.group(1)

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\s+(component|%s|component\s+%s)\b' % (name, name), pline):
			end_line = l
			break
	if end_line < 0:
		return False, 0  # could not find end of function

	CheckComponent(filename, clean_lines, start_line, end_line, name, error)
	return True, end_line


def CheckArchitecture(filename, clean_lines, start_line, end_line, name, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected architecture \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddOtherIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)

	# check for blank line before block. Allow comments
	if not IsPrevLineBlankOrComment(clean_lines, start_line):
		error(filename, LineRef.OnlyLine(start_line), 'whitespace/blank_line', 4, 'Blank line should come before architecture declaration.')
	# check for blank line after block. Allow comments
	if not IsNextLineBlankOrComment(clean_lines, start_line):
		error(filename, LineRef.OnlyLine(start_line), 'whitespace/blank_line', 4, 'Blank line should come after architecture declaration.')

	l = start_line
	# check for architecture items before 'begin'
	while l <= end_line:
		pline = clean_lines.lines[l]

		# detect functions and process separately
		(f_match, f_end_line) = CheckFunctions(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over function
			continue

		# detect procedures and process separately
		(f_match, f_end_line) = CheckProcedures(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over procedure
			continue

		# detect components and process separately
		(f_match, f_end_line) = CheckComponents(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over component
			continue

		# detect records and process separately
		(f_match, f_end_line) = CheckRecords(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over record
			continue

		# TODO improve checking to not detect other structures with begin, like functions
		if Match(r'\s*\bbegin\b', pline):
			break

		# check used identifiers in other signal declarations
		CheckIdentifiers(filename, clean_lines, l, error)

		# detect constant declarations
		CheckConstants(filename, clean_lines, l, error)

		# detect signal declarations
		CheckSignals(filename, clean_lines, l, error)

		# detect type declarations
		CheckTypes(filename, clean_lines, l, error)

		# detect assert statements
		CheckAsserts(filename, clean_lines, l, error)

		# next line
		l = l + 1

	# on architecture begin

	# check for blank line before block. Allow comments
	if not IsPrevLineBlankOrComment(clean_lines, l):
		error(filename, LineRef.OnlyLine(l), 'whitespace/blank_line', 4, 'Blank line should come before architecture begin.')
	# check for blank line after block. Allow comments
	if not IsNextLineBlankOrComment(clean_lines, l):
		error(filename, LineRef.OnlyLine(l), 'whitespace/blank_line', 4, 'Blank line should come after architecture begin.')

	# check architecture body after 'begin'
	while l <= end_line:
		pline = clean_lines.lines[l]

		# detect port maps and process separately
		(f_match, f_end_line) = CheckPortMaps(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over procedure
			continue

		(f_match, f_end_line) = CheckProcesses(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over procedure
			continue

		CheckIdentifiers(filename, clean_lines, l, error)

		CheckAsserts(filename, clean_lines, l, error)

		# next line
		l = l + 1

	# check for blank line before block. Allow comments
	if not IsPrevLineBlankOrComment(clean_lines, end_line):
		error(filename, LineRef.OnlyLine(end_line), 'whitespace/blank_line', 4, 'Blank line should come before architecture end.')


def CheckArchitectures(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match = Match(r'\s*\barchitecture\s+(.+?)\s+of\s+(.+?)\s+is', line)
	if not match:
		return

	name = match.group(1)
	start_line = line_num
	end_line = -1

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\s+(architecture|%s|architecture\s+%s)\b' % (name, name), pline):
			end_line = l
			break
	if end_line < 0:
		return  # could not find end of architecture

	CheckArchitecture(filename, clean_lines, start_line, end_line, name, error)


def CheckGenerics(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match = Search(r'\bgeneric\s*\(', line)
	if match:
		# This could be a multiline
		pos = match.end() - 1
		(string, el, endpos) = ExtractExpression(clean_lines, line_num, pos)
		pos += 1  # skip open parenthesis
		endpos -= 1  # skip end parenthesis
		l = line_num
		while l <= el:
			pline = clean_lines.lines[l]
			ep = endpos if l == el else None  # use endpos on last line
			match, decl_type, name_list, mode, stype, init, pos = MatchDeclaration(filename, clean_lines, l, error, pos, check_int_range=False, endpos=ep)
			if not match:
				l = l + 1
				continue

			# keep the same line to check again
			for name in name_list:
				_lint_state.PrintVerbose("Detected generic declaration \'%s\' : %s := %s\n" % (name, stype, init))
				lineref = LineRef.FromString(l, pline, name)
				AddConstantIdentifier(name, stype, init, lineref)
				idt = GetIdentifierWithType(name)
				# add driver for constants
				idt.AddDriver(Driver("", l))

				if not name.isupper():
					error(filename, lineref, 'readability/constants', 1, 'Invalid capitalization on \'%s\'. Generic names should use all upper case.' % name)
				if not name.upper().startswith('G_'):
					error(filename, lineref, 'readability/naming', 1, 'Invalid naming convention on \'%s\'. Generic names should use prefix \'G_\'.' % name)


def CheckPorts(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match = Search(r'\bport\s*\(', line)
	if match:
		# This could be a multiline
		pos = match.end() - 1
		(string, endline, endpos) = ExtractExpression(clean_lines, line_num, pos)

		# check used identifiers first before new declarations
		for l in xrange(line_num, endline + 1):
			CheckIdentifiers(filename, clean_lines, l, error)

		pos += 1  # skip open parenthesis
		endpos -= 1  # skip end parenthesis
		l = line_num
		while l <= endline:
			pline = clean_lines.lines[l]
			ep = endpos if l == endline else None  # use endpos on last line
			match, decl_type, name_list, mode, stype, init, pos = MatchDeclaration(filename, clean_lines, l, error, pos, endpos=ep)
			if not match:
				l = l + 1
				continue

			# keep the same line to check again

			# check type ranges
			base_stype = stype
			match = Match(r'(\w+)\s*(\(.*?\))?', stype)
			if match:
				base_stype = match.group(1)

			for name in name_list:
				_lint_state.PrintVerbose("Detected port declaration \'%s\'/%s/%s/%s\n" % (name, mode, stype, init))
				AddPortIdentifier(name, stype, init, mode, LineRef.FromString(l, pline, name), filename, error)
				idt = GetIdentifierWithType(name)
				# add driver for inputs
				if mode.lower() == "in" or mode.lower() == "inout":
					idt.AddDriver(Driver("", l))

				port_modes = ["in", "out", "inout"]
				if mode.lower() not in port_modes:
					error(filename, LineRef.FromString(l, pline, mode), 'build/port_modes', 1, 'Invalid port mode \'%s\'. Allowed modes are %s' % (mode, port_modes))

				# TODO allow records?
				port_types = ["std_logic", "std_logic_vector"]
				if base_stype.lower() not in port_types:
					error(filename, LineRef.FromString(l, pline, base_stype), 'build/port_types', 1, 'Invalid port type \'%s\'. Allowed types are %s' % (base_stype, port_types))

	return


def CheckEntity(filename, clean_lines, start_line, end_line, name, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected entity \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddOtherIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)

		# check for blank line before block. Allow comments
	if not IsPrevLineBlankOrComment(clean_lines, start_line):
		error(filename, LineRef.OnlyLine(start_line), 'whitespace/blank_line', 4, 'Blank line should come before entity declaration.')

	# check that filename contains the entity name
	if name.lower() not in filename:
		error(filename, LineRef.OnlyLine(start_line), 'build/filename', 1, 'Filename should contain entity name \'%s\'' % name.lower())

	for l in xrange(start_line, end_line):
		pline = clean_lines.lines[l]

		# detect generic declarations process separately
		CheckGenerics(filename, clean_lines, l, error)

		# detect port declarations process separately
		CheckPorts(filename, clean_lines, l, error)

	# check for blank line after block. Allow comments
	if not IsNextLineBlankOrComment(clean_lines, end_line):
		error(filename, LineRef.OnlyLine(end_line), 'whitespace/blank_line', 4, 'Blank line should come after entity end.')


def CheckEntities(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match = Match(r'\s*\bentity\s+(.+?)\s+is', line)
	if not match:
		return

	name = match.group(1)
	start_line = line_num
	end_line = -1

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\s+(entity|%s|entity\s+%s)\b' % (name, name), pline):
			end_line = l
			break
	if end_line < 0:
		return  # could not find end of process

	CheckEntity(filename, clean_lines, start_line, end_line, name, error)


def CheckPackage(filename, clean_lines, start_line, end_line, name, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected package \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddOtherIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)

	# check for blank line before block. Allow comments
	if not IsPrevLineBlankOrComment(clean_lines, start_line):
		error(filename, LineRef.OnlyLine(start_line), 'whitespace/blank_line', 4, 'Blank line should come before package declaration.')
	# check for blank line after block. Allow comments
	if not IsNextLineBlankOrComment(clean_lines, start_line):
		error(filename, LineRef.OnlyLine(start_line), 'whitespace/blank_line', 4, 'Blank line should come after package declaration.')

	l = start_line
	while l <= end_line:
		line = clean_lines.lines[l]

		# detect function declarations
		(f_match, f_end_line) = CheckFunctionDeclarations(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over function
			continue

		(f_match, f_end_line) = CheckProcedureDeclarations(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over function
			continue

		# detect records and process separately
		(f_match, f_end_line) = CheckRecords(filename, clean_lines, l, error)
		if f_match:
			l = f_end_line + 1  # skip over record
			continue

		# check used identifiers
		CheckIdentifiers(filename, clean_lines, l, error)

		# detect constant declarations
		CheckConstants(filename, clean_lines, l, error, in_pkg=True)

		# detect type declarations
		CheckTypes(filename, clean_lines, l, error, in_pkg=True)

		# next line
		l = l + 1

	# check for blank line before block. Allow comments
	if not IsPrevLineBlankOrComment(clean_lines, end_line):
		error(filename, LineRef.OnlyLine(end_line), 'whitespace/blank_line', 4, 'Blank line should come before package end.')
	# check for blank line after block. Allow comments
	if not IsNextLineBlankOrComment(clean_lines, end_line):
		error(filename, LineRef.OnlyLine(end_line), 'whitespace/blank_line', 4, 'Blank line should come after package end.')


def CheckPackages(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match = Match(r'\s*\bpackage\s+(\w+?)\s+is', line)
	if not match:
		return

	name = match.group(1)
	start_line = line_num
	end_line = -1

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\s+(package|%s|package\s+%s)\b' % (name, name), pline):
			end_line = l
			break
	if end_line < 0:
		return  # could not find end of process

	CheckPackage(filename, clean_lines, start_line, end_line, name, error)


def CheckPackageBody(filename, clean_lines, start_line, end_line, name, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected package body \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	AddOtherIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)

	# check for blank line before block. Allow comments
	if not IsPrevLineBlankOrComment(clean_lines, start_line):
		error(filename, LineRef.OnlyLine(start_line), 'whitespace/blank_line', 4, 'Blank line should come before package body declaration.')
	# check for blank line after block. Allow comments
	if not IsNextLineBlankOrComment(clean_lines, start_line):
		error(filename, LineRef.OnlyLine(start_line), 'whitespace/blank_line', 4, 'Blank line should come after package body declaration.')

	l = start_line
	while l <= end_line:
		pline = clean_lines.lines[l]

		# detect functions and process separately
		(f_match, f_end_line) = CheckFunctions(filename, clean_lines, l, error, in_pkg=True)
		if f_match:
			l = f_end_line + 1  # skip over function
			continue

		# detect procedures and process separately
		(f_match, f_end_line) = CheckProcedures(filename, clean_lines, l, error, in_pkg=True)
		if f_match:
			l = f_end_line + 1  # skip over procedure
			continue

		# detect constant declarations
		CheckConstants(filename, clean_lines, l, error, in_pkg=True)

		# check used identifiers
		CheckIdentifiers(filename, clean_lines, l, error)

		# next line
		l = l + 1

	# check for blank line before block. Allow comments
	if not IsPrevLineBlankOrComment(clean_lines, end_line):
		error(filename, LineRef.OnlyLine(end_line), 'whitespace/blank_line', 4, 'Blank line should come before package body end.')


def CheckPackageBodies(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match = Match(r'\s*\bpackage\s+body\s+(\w+?)\s+is', line)
	if not match:
		return

	name = match.group(1)
	start_line = line_num
	end_line = -1

	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\s+(package\s+body|%s|package\s+body\s+%s)\b' % (name, name), pline):
			end_line = l
			break
	if end_line < 0:
		return  # could not find end of process

	CheckPackageBody(filename, clean_lines, start_line, end_line, name, error)


def CheckLoop(filename, clean_lines, start_line, end_line, name, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected loop \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	if name:
		AddOtherIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)

	pline = clean_lines.lines[start_line]

	# check type of loop
	if Match(r'.*?\bwhile.*?\bloop\b', pline):
		# while loop
		pass
	elif Match(r'.*?\bfor.*?\bloop\b', pline):
		# for loop
		pass
	else:
		# loop
		wait_found = False
		exit_found = False
		for l in xrange(start_line, end_line):
			if Match(r'.*?\bwait\b', clean_lines.lines[l]):
				wait_found = True
				break
			if Match(r'.*?\bexit\b', clean_lines.lines[l]):
				exit_found = True
				break

		if not wait_found and not exit_found:
			error(filename, LineRef.OnlyLine(start_line), 'runtime/loops', 4, 'Infinite loop. Loop must contain wait or exit statement.')


def CheckCaseStatement(filename, clean_lines, start_line, end_line, label, name, is_sequential, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected case statement \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	if label:
		AddOtherIdentifier(label, LineRef.FromString(start_line, line, label), filename, error)

	current_state = None

	for l in xrange(start_line, end_line):
		pline = clean_lines.lines[l]

		# look for start of states, when XX =>
		match = Match(r'.*?\bwhen\s+(.*?)\s*=>', pline)
		if match:
			current_state = match.group(1)

		if is_sequential:
			# look for assignments of state, state <= xxx
			match = Match(r'.*?((.*?)\s*[<:]\=(.*?))\s*;', pline)
			if match:
				stmt = match.group(1).strip()
				lhs = match.group(2).strip()
				rhs = match.group(3).strip()

				if lhs.lower() == name.lower() and rhs.lower() == current_state.lower():
					error(filename, LineRef.FromString(l, pline, stmt), 'readability/fsm', 4, 'Redundant assignment of state \'%s\' to \'%s\'' % (name, current_state))


def FindUsedVariables(line, direct_lhs_name=False):
	write = set()
	read = set()
	# check for assignments
	match = Match(r'.*?' + _PATTERN_IDENTIFIER_USE + '\s*[<:]\=(.*);', line)
	if match:
		if direct_lhs_name == True:
			# use lhs as given
			lhs = match.group(1)
			write_words = [lhs]
		else:
			# use only signal and not range
			lhs = match.group(2)
			write_words = re.findall(r'\b[\w\']+\b', lhs)
		write = set([i for i in write_words if IsSignalIdentifier(i)])

		rhs = match.group(4)
		read_words = re.findall(r'\b[\w\']+\b', rhs)
		is_assign = True
	else:
		read_words = re.findall(r'\b[\w\']+\b', line)
		is_assign = False

	read = set([i for i in read_words if IsSignalIdentifier(i)])

	return (write, read, is_assign)


def CheckProcess(filename, clean_lines, start_line, end_line, name, sensitivity_list, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected process \'%s\' on lines %d-%d (%s)\n" % (name, start_line, end_line, sensitivity_list))
	if name:
		AddOtherIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)
	global _drivers
	process_drivers = set()
	process_inputs = set()
	contains_all = False

	AddLocalScope()

	sline = clean_lines.lines[start_line]

	# check for VHDL 2008 process(all)
	if 'all' in sensitivity_list:
		contains_all = True
		error(filename, LineRef.FromString(start_line, sline, "all"), 'build/vhdl2008/sensitivity', 4, 'Avoid VHDL2008 construct \'all\' in sensitivity list.')

	# detect duplicates in the sensitivity list
	dups = [k for k, v in Counter(sensitivity_list).items() if v > 1]
	for d in dups:
		error(filename, LineRef.FromStringR(start_line, sline, d), 'runtime/sensitivity', 4, 'Duplicate signal \'%s\' in sensitivity list.' % d)

	# if there are items in the sensitivity list, then we are not a simulation process
	sim_process = len(sensitivity_list) == 0

	# determine if this is a sequential or combinational process
	sequential = False
	clk_name = ""
	clk_line = 0
	for l in xrange(start_line, end_line):
		pline = clean_lines.lines[l]
		match = Match(r'.*?(' + _PATTERN_IDENTIFIER_USE + ')\'event', pline)
		clk_line = l
		if match:
			sequential = True
			clk_name = match.group(1)
			break

		match = Match(r'.*\brising_edge\s*\((' + _PATTERN_IDENTIFIER_USE + ')\)', pline)
		if match:
			sequential = True
			clk_name = match.group(1)
			break

		match = Match(r'.*\bfalling_edge\s*\((' + _PATTERN_IDENTIFIER_USE + ')\)', pline)
		if match:
			sequential = True
			clk_name = match.group(1)
			break

	if not sim_process and sequential:
		# clock must be in sensitivity list
		if clk_name.lower() not in sensitivity_list and not contains_all:
			error(filename, LineRef.FromString(clk_line, clean_lines.lines[clk_line], clk_name), 'runtime/sensitivity', 5, 'Missing clock \'%s\' from sensitivity list' % (clk_name))

		# must have clk_ prefix or _clk suffix or _clk_i suffix
		if (not Match(r'^(\w+.)?clk.*', clk_name)
			and not Match(r'.*clk$', clk_name)
			and not Match(r'.*clk_i$', clk_name)):
			error(filename, LineRef.FromString(clk_line, clean_lines.lines[clk_line], clk_name), 'readability/naming', 1, 'Invalid naming convention on clock signal \'%s\'. Allowed conventions are [clk_*, *_clk, *_clk_i].' % clk_name)

		# if sequential process, only need clock and maybe async reset
		# warn on more that 2 items in sensitivity list
		if len(sensitivity_list) > 2:
			error(filename, LineRef.OnlyLine(start_line), 'runtime/sensitivity', 4, 'Superfluous items in sensitivity list. Sequential processes should have at most 2 items (clock, async reset).')

	l = start_line
	while l <= end_line:
		pline = clean_lines.lines[l]

		# check used identifiers
		CheckIdentifiers(filename, clean_lines, l, error)

		# detect functions and process separately
		(f_match, f_end_line) = CheckFunctions(filename, clean_lines, l, error, in_pkg=True)
		if f_match:
			l = f_end_line + 1  # skip over function
			continue

		# detect procedures and process separately
		(f_match, f_end_line) = CheckProcedures(filename, clean_lines, l, error, in_pkg=True)
		if f_match:
			l = f_end_line + 1  # skip over procedure
			continue

		# check variables, don't check integer ranges for simulation processes
		names, stype, init = CheckVariables(filename, clean_lines, l, error, check_int_range=not sim_process)
		if names:
			if not sim_process:
				error(filename, LineRef.FromString(l, pline, names[0]), 'runtime/variables', 4, 'Variables are easily misused and should be avoided.')

		# check constants
		CheckLocalConstants(filename, clean_lines, l, error)

		# skip until we find 'begin'
		if Match(r'.*\bbegin\b', pline):
			break

		# next line
		l = l + 1

	# check process body after 'begin'
	body_line = l
	for l in xrange(body_line, end_line):
		pline = clean_lines.lines[l]

		l_match = Match(r'\s*((.*?)\s*:)?.*\bcase\s+(.+?)\s+is', pline)
		if l_match:
			label = l_match.group(2)
			name = l_match.group(3)
			l_end_line = -1
			# find the end line of the process
			for l_l in xrange(l, end_line):
				if Match(r'.*\bend\s+case(\s+%s)?\b' % (label), clean_lines.lines[l_l]):
					l_end_line = l_l
					break
			if l_end_line < 0:
				return  # could not find end of function
			CheckCaseStatement(filename, clean_lines, l, l_end_line, label, name, sequential, error)

		# detect loops and process separately
		l_match = Match(r'\s*((.*?)\s*:)?.*\bloop\b\s*$', pline)
		if l_match:
			label = l_match.group(2)
			l_end_line = -1
			# find the end line of the process
			for l_l in xrange(l, end_line):
				if Match(r'.*\bend\s+loop(\s+%s)?\b' % (label), clean_lines.lines[l_l]):
					l_end_line = l_l
					break
			if l_end_line < 0:
				return  # could not find end of function
			CheckLoop(filename, clean_lines, l, l_end_line, label, error)

		if not sim_process:
			match = Match(r'.*?(\w+)\'event', pline)
			if match:
				name = match.group(1)
				error(filename, LineRef(l, match.start(1), match.end(1)), 'runtime/rising_edge', 4, 'Use \'rising_edge/falling_edge(%s)\' instead of \'%s\'event\'' % (name, name))

		(write_vars, read_vars, is_assign) = FindUsedVariables(pline)
		for w in write_vars:
			process_drivers.add(w.lower())
			if IsIdentifierWithType(w):
				idt = GetIdentifierWithType(w)
				idt.AddDriver(ProcessDriver(start_line, l))

		for r in read_vars:
			process_inputs.add(r.lower())

		# check used identifiers
		CheckIdentifiers(filename, clean_lines, l, error)

		CheckAsserts(filename, clean_lines, l, error)

		# check if this signal has been written by multiple processes, i.e. multiple drivers
		# TODO add support for detecting writing outside of processes
		for w in write_vars:
			if IsIdentifierWithType(w):
				idt = GetIdentifierWithType(w)
				if idt.HasMultipleDrivers():
					# build a list of line numbers
					line_str = ""
					for d in idt.GetDrivers()[:-1]:
						line_str += '%d,' % d.line
					error(filename, LineRef.FromString(l, pline, w), 'runtime/multiple_drivers', 5, 'Multiple drivers on signal \'%s\'. Previous drivers are on line(s): %s.' % (w, line_str.rsplit(',', 1)[0]))

		# check sensitivity list
		if not sim_process and not sequential:
			for r in read_vars:
				if r.lower() not in sensitivity_list and not contains_all:
					error(filename, LineRef.FromString(l, pline, r), 'runtime/sensitivity', 5, 'Missing signal \'%s\' from sensitivity list' % (r))

	# check for extra items in the sensitivity list
	# that don't need to be there.
	for item in sensitivity_list:
		if item not in process_inputs and item != 'all':
			error(filename, LineRef.FromString(start_line, sline, item), 'runtime/sensitivity', 4, 'Extra signal \'%s\' in sensitivity list.' % item)

	# check for combinational loop
	# this is when we have a non-sequential process
	# and one of the outputs is also an input
	if not sim_process and not sequential:
		inter = process_drivers.intersection(process_inputs)
		for i in inter:
			error(filename, LineRef.OnlyLine(start_line), 'runtime/combinational_loop', 5, 'Possible combinational loop detected on signal \'%s\'.' % (i))

	# add all written values to the driver list
	# next time this value is written from outside this process
	# we will throw an error
	_drivers = _drivers | process_drivers

	RemoveLocalScope(filename, error)


def CheckProcesses(filename, clean_lines, line_num, error):

	def allowed_in_sensitivity(i):
		if i.lower() == 'all':
			return True
		if IsSignalIdentifier(i):
			return True
		if IsReservedWord(i):
			return False
		return False

	line = clean_lines.lines[line_num]
	match = Match(r'\s*((.*?)\s*:)?\s*\bprocess\b\s*(\((.*)\))?', line)
	if not match:
		return False, 0

	label = match.group(2)
	start_line = line_num
	end_line = -1
	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\bend\s+(process|%s|process\s+%s)\b' % (label, label), pline):
			end_line = l
			break
	if end_line < 0:
		return False, 0  # could not find end of process

	# see if there is a sensitivity list
	sensitivity_list = []
	match = Search(r'\bprocess\s*\(', line)
	if match:
		# This could be a multiline
		pos = match.end() - 1
		(string, endline, endpos) = ExtractExpression(clean_lines, line_num, pos)
		sensitivity_list = re.findall(r'\b[\w\']+\b', string.lower())
		sensitivity_list = [i for i in sensitivity_list if allowed_in_sensitivity(i)]

	CheckProcess(filename, clean_lines, start_line, end_line, label, sensitivity_list, error)

	return True, end_line


def CheckPortMap(filename, clean_lines, start_line, end_line, name, error):
	line = clean_lines.lines[start_line]
	_lint_state.PrintVerbose("Detected port map \'%s\' on lines %d-%d\n" % (name, start_line, end_line))
	if name:
		AddOtherIdentifier(name, LineRef.FromString(start_line, line, name), filename, error)

	for l in xrange(start_line, end_line):
		line = clean_lines.lines[l]

		# see if there is a sensitivity list
		match = Search(r'\bport\s+map\s*\(', line)
		if match:
			# This could be a multiline
			pos = match.end() - 1
			(string, endline, endpos) = ExtractExpression(clean_lines, l, pos)
			map_list = re.split(r',(?![^\(]*[\)])', "".join(string.split()))  # remove whitespace before splitting

			# handle nested parenthesis
			i = 0
			while i < len(map_list):
				if map_list[i].count('(') != map_list[i].count(')'):
					# merge two items
					map_list[i:i+2] = [''.join(map_list[i:i+2])]
					# repeat this index
				else:
					i = i + 1

			# map_list = "".join(string).split(",")
			for mapping in map_list:
				items = mapping.split("=>", 1)
				if not Match(r'.*=>.*', mapping):
					_lint_state.PrintVerbose("port mapping \'%s\''\n" % (items[0]))
					rhs = items[0]
					error(filename, LineRef.OnlyLine(l), 'readability/portmaps', 4, 'Positional port mapping not allowed. Use named mapping.')
				else:
					_lint_state.PrintVerbose("port mapping \'%s\' => \'%s\''\n" % (items[0], items[1]))
					rhs = items[1]

				CheckIdentifiersString(filename, rhs, l, error)

				if IsIdentifierWithType(rhs):
					idt = GetIdentifierWithType(rhs)
					# for port maps, say the item is both read and written since we can't distinguish
					idt.AddDriver(PossibleDriver("", l))
			break


def CheckPortMaps(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match = Match(r'\s*((.*?)\s*:)?\s*\bport map', line)
	if not match:
		return False, 0

	label = match.group(2)
	start_line = line_num
	end_line = -1
	# find the end line of the process
	for l in xrange(line_num, clean_lines.NumLines()):
		pline = clean_lines.lines[l]
		if Match(r'.*\);', pline):
			end_line = l
			break
	if end_line < 0:
		return False, 0  # could not find end of process

	CheckPortMap(filename, clean_lines, start_line, end_line, label, error)

	return True, end_line


def CheckIdentifiersString(filename, line, line_num, error):
	# skip strings in quotes
	words = re.findall(r"[\"].*?[\"]|[\'].*?[\']|(\w+)", line)
	for w in words:
		if IsIdentifier(w):
			# mark identifier as used
			i = GetIdentifier(w)
			i.IncRefs()
			_lint_state.PrintVerbose("Detected reference of identifier \'%s\' on line %d\n" % (w, line_num))
			# check for consistent capitalization on identifiers
			if w != i.Name():
				error(filename, LineRef.FromString(line_num, line, w), 'readability/capitalization', 1, 'Inconsistent capitalization on identifier \'%s\'. Declared as \'%s\' on line %d' % (w, i.Name(), i.Line()))


def CheckIdentifiers(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	CheckIdentifiersString(filename, line, line_num, error)

	(write_vars, read_vars, is_assign) = FindUsedVariables(line)
	if is_assign:
		CheckReadIdentifiers(filename, clean_lines, line_num, error, read_vars)

def CheckReadIdentifiers(filename, clean_lines, line_num, error, read_vars):
	line = clean_lines.lines[line_num]
	for r in read_vars:
		if IsIdentifierWithType(r):
			idt = GetIdentifierWithType(r)
			if isinstance(idt, Port) and idt.mode.lower() == "out":
				error(filename, LineRef.FromString(line_num, line, r), 'build/vhdl2008/outputs', 4, 'Avoid VHDL2008 reading of output port on \'%s\'.' % r)


def CheckCondition(filename, clean_lines, line_num, error, cond):
	line = clean_lines.lines[line_num]
	# look for +,-,*,/ in if statement conditions
	matches = re.findall(r'('+_PATTERN_IDENTIFIER_USE + r'\s*(\+|\-|\*|\/)\s*' + _PATTERN_IDENTIFIER_USE+r')', cond)
	for match in matches:
		expr = match[0]
		w1 = match[1]
		op = match[4]
		w2 = match[5]
		# allow expressions on constants
		if IsSignalOrVariableIdentifier(w1) or IsSignalOrVariableIdentifier(w2):
			error(filename, LineRef.FromString(line_num, line, expr), 'build/arithmetic', 4, 'Avoid arithmetic operations on signals in conditional checks.')

	# look for items not followed by an operator
	# skip strings in quotes, and function calls params
	pat = r'[\"\'].*?[\"\']|.+?\s*(<=|>=|<|>|=|\/=|\+|\-|\*|\/)\s*.+|' + _PATTERN_IDENTIFIER_USE
	matches = re.findall(pat, cond)
	for match in matches:
		w1 = match[2]
		if IsIdentifierWithType(w1):
			idt = GetIdentifierWithType(w1)
			if not idt.IsBoolean():
				error(filename, LineRef.FromString(line_num, line, w1), 'build/vhdl2008', 4, 'Avoid VHDL2008 \'boolean style\' conditional on \'%s\'.' % w1)

	# check all identifiers used in the condition
	(write_vars, read_vars, is_assign) = FindUsedVariables(line)
	CheckReadIdentifiers(filename, clean_lines, line_num, error, read_vars)


def CheckBooleans(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	matches = re.findall(r'.*?\s*((\w+)\s*(\/?=)\s*(\w+))', line)
	for match in matches:
		expr = match[0]
		w1 = match[1]
		op = match[2]
		w2 = match[3]
		if w1.lower() == 'true' or w1.lower() == 'false' or w2.lower() == 'true' or w2.lower() == 'false':
			error(filename, LineRef.FromString(line_num, line, expr), 'readability/booleans', 1, 'Redundant boolean equality check. Use \'VALUE\' instead of \'VALUE = true\', and \'not VALUE\' instead of \'VALUE = false\'')

	# look for if statements
	match = Search(r'\b(if|elsif)\b(.*?)\bthen\b', line)
	if match:
		cond = match.group(2)
		CheckCondition(filename, clean_lines, line_num, error, cond)

	# look for when...else
	match = Match(r'.*?\b\w+\b\s*[<:]=\s*((.*?)\s*\bwhen\b\s*(.*?)\s*(\belse\b\s*(.*?)\s*)?)+;', line)
	if match:
		matches = re.findall(r'\bwhen\b\s*(.*?)\s*(\belse\b|;)', line)
		for m in matches:
			cond = m[0]
			CheckCondition(filename, clean_lines, line_num, error, cond)


def CheckAsserts(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]

	# TODO support multiple line asserts
	match = Match(r'\s*\bassert\b\s+(.*?)\s+(report|$)', line)
	if match:
		cond = match.group(1)
		_lint_state.PrintVerbose("Detected assert \'%s\' \n" % (cond))

		CheckCondition(filename, clean_lines, line_num, error, cond)


def CheckConstants(filename, clean_lines, line_num, error, in_pkg=False):
	line = clean_lines.lines[line_num]
	match, decl_type, name_list, direction, stype, init, pos = MatchDeclaration(filename, clean_lines, line_num, error, req_decl_type='constant')
	if not match:
		return None, None, None

	for name in name_list:
		_lint_state.PrintVerbose("Detected constant declaration \'%s\' : %s := %s\n" % (name, stype, init))
		AddConstantIdentifier(name, stype, init, LineRef.FromString(line_num, line, name))
		idt = GetIdentifierWithType(name)
		# add driver for constants
		idt.AddDriver(Driver("", line_num))

		# in a package we assume the identifier will be used externally
		if in_pkg:
			idt.IncRefs()  # mark identifier as used

		if not name.isupper():
			error(filename, LineRef.FromString(line_num, line, name), 'readability/constants', 1, 'Invalid capitalization on \'%s\'. Constant names should use all upper case.' % name)
		if not name.upper().startswith('C_'):
			error(filename, LineRef.FromString(line_num, line, name), 'readability/naming', 1, 'Invalid naming convention on \'%s\'. Constant names should use prefix \'C_\'.' % name)


def CheckSignals(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match, decl_type, name_list, direction, stype, init, pos = MatchDeclaration(filename, clean_lines, line_num, error, req_decl_type='signal')
	if not match:
		return None, None, None

	for name in name_list:
		_lint_state.PrintVerbose("Detected signal declaration \'%s\' : %s := %s\n" % (name, stype, init))
		AddSignalIdentifier(name, stype, init, LineRef.FromString(line_num, line, name), filename, error)


def CheckTypes(filename, clean_lines, line_num, error, in_pkg=False):
	line = clean_lines.lines[line_num]

	# detect type declarations
	match = Search(r'.*\btype\s+(\w+)\s+is\s*\(', line)
	if match:
		name = match.group(1)
		# This could be a multiline
		pos = match.end() - 1
		(string, endline, endpos) = ExtractExpression(clean_lines, line_num, pos)
		enum_vals = "".join(string.split()).split(",")  # remove whitespace before splitting
		AddReferencedIdentifier(name, LineRef.FromString(line_num, line, name), filename, error)
		_lint_state.PrintVerbose("Detected type declaration \'%s\' is %s\n" % (name, enum_vals))
		# in a package we assume the identifier will be used externally
		if in_pkg:
			idt = GetIdentifier(name)
			idt.IncRefs()  # mark identifier as used

		for val in enum_vals:
			if not val.isupper():
				error(filename, LineRef.FromString(line_num, line, val), 'readability/constants', 1, 'Invalid capitalization on \'%s\'. Enum values should use all upper case.' % val)

			# look for FSM states
			# must have ST_ prefix or _ST suffix
			if 'state' in name.lower() or 'fsm' in name.lower():
				if not Match(r'.*_ST$', val.upper()) and not Match(r'^ST_.*', val.upper()):
					error(filename, LineRef.FromString(line_num, line, val), 'readability/naming', 1, 'Invalid naming convention on enum FSM type \'%s\'. Enum type names should use ST_ or _ST.' % val)

	# detect subtype declarations
	match = Search(r'.*\bsubtype\s+(\w+)\s+is\s*', line)
	if match:
		name = match.group(1)
		AddReferencedIdentifier(name, LineRef.FromString(line_num, line, name), filename, error, enforce_caps=False)
		_lint_state.PrintVerbose("Detected subtype declaration \'%s\'\n" % (name))
		# in a package we assume the identifier will be used externally
		if in_pkg:
			idt = GetIdentifier(name)
			idt.IncRefs()  # mark identifier as used

	# detect alias declarations
	match = Search(r'.*\balias\s+(\w+)\b', line)
	if match:
		name = match.group(1)
		AddReferencedIdentifier(name, LineRef.FromString(line_num, line, name), filename, error)
		_lint_state.PrintVerbose("Detected alias declaration \'%s\'\n" % (name))
		# in a package we assume the identifier will be used externally
		if in_pkg:
			idt = GetIdentifier(name)
			idt.IncRefs()  # mark identifier as used


def MatchDeclaration(filename, clean_lines, line_num, error, pos=0, check_int_range=True, req_decl_type=None, endpos=None):
	oline = clean_lines.lines[line_num]
	# substring based on pos and endpos
	if endpos is not None:
		oline = oline[:endpos]
	line = oline[pos:]

	match = Match(r'\s*(\b(variable|signal|constant)\b)?\s*(.+?)\s*:\s*(\b\w+\b)?\s*(\b\w[^;:]+)\s*(:=\s*([^;]+))?;?', line)
	if not match:
		return False, None, None, None, None, None, 0

	decl_type = match.group(2)
	names = match.group(3)
	direction = match.group(4)
	stype = match.group(5)
	init = match.group(7)
	pos = pos + match.end()

	if decl_type is not None:
		decl_type = decl_type.lower().strip()

	# check against requested type
	if (req_decl_type is not None) and (req_decl_type != decl_type):
		# not the requested declaration type
		return False, None, None, None, None, None, 0

	if direction is not None:
		direction = direction.strip()
	if stype is not None:
		stype = stype.strip()
	if init is not None:
		init = init.strip()

	name_list = "".join(names.split()).split(",")  # remove whitespace before splitting

	# check for init, multiline records inits
	match = Search(r':=\s*\(\s*', line[pos:])
	if match:
		# This could be a multiline
		pos = match.end() - 1
		(string, endline, endpos) = ExtractExpression(clean_lines, line_num, pos)
		init = "".join(string.split())  # remove whitespace
		init = '(' + init + ')'

	if len(name_list) > 1:
		error(filename, LineRef.FromString(line_num, oline, names), 'readability/declarations', 1, 'Avoid using multiple declarations per line.')

	if decl_type != "constant" and check_int_range:
		if stype == "integer":
			error(filename, LineRef.FromString(line_num, oline, stype), 'runtime/integers', 5, 'Integer types must have a range specified.')
		if stype == "natural":
			error(filename, LineRef.FromString(line_num, oline, stype), 'runtime/integers', 5, 'Natural types must have a range specified.')
		if stype == "positive":
			error(filename, LineRef.FromString(line_num, oline, stype), 'runtime/integers', 5, 'Positive types must have a range specified.')

	return True, decl_type, name_list, direction, stype, init, pos


def CheckVariables(filename, clean_lines, line_num, error, check_int_range=True):
	line = clean_lines.lines[line_num]
	match, decl_type, name_list, direction, stype, init, pos = MatchDeclaration(filename, clean_lines, line_num, error, check_int_range=check_int_range, req_decl_type='variable')
	if not match:
		return None, None, None

	for name in name_list:
		_lint_state.PrintVerbose("Detected local \'%s\' : %s := %s on line %d\n" % (name, stype, init, line_num))

		# check shadowed variables
		if IsReferencedIdentifier(name):
			i = GetIdentifier(name)
			if not isinstance(i, LocalIdentifier):# make sure this isn't another variable declared elsewhere
				error(filename, LineRef.FromString(line_num, line, name), 'build/shadow', 4, 'Local variable \'%s\' shadows previously declared identifier. Previous declared on line %d.' % (name, i.Line()))
				error(filename, i.lineref, 'build/shadow', 4, 'Identifier is shadowed by later declared local variable \'%s\'.' % (name))

		AddLocalIdentifier(name, stype, init, LineRef.FromString(line_num, line, name), filename, error)

	return name_list, stype, init


def CheckLocalConstants(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	match, decl_type, name_list, direction, stype, init, pos = MatchDeclaration(filename, clean_lines, line_num, error, check_int_range=False, req_decl_type='constant')
	if not match:
		return None, None, None

	for name in name_list:
		_lint_state.PrintVerbose("Detected local constant \'%s\' : %s := %s on line %d\n" % (name, stype, init, line_num))

		# check shadowed variables
		if IsReferencedIdentifier(name):
			i = GetIdentifier(name)
			if not isinstance(i, LocalIdentifier):# make sure this isn't another variable declared elsewhere
				error(filename, LineRef.FromString(line_num, line, name), 'build/shadow', 4, 'Local constant \'%s\' shadows previously declared identifier. Previous declared on line %d.' % (name, i.Line()))
				error(filename, i.lineref, 'build/shadow', 4, 'Identifier is shadowed by later declared local constant \'%s\'.' % (name))

		if not name.isupper():
			error(filename, LineRef.FromString(line_num, line, name), 'readability/constants', 1, 'Invalid capitalization on \'%s\'. Constant names should use all upper case.' % name)
		if not name.upper().startswith('C_'):
			error(filename, LineRef.FromString(line_num, line, name), 'readability/naming', 1, 'Invalid naming convention on \'%s\'. Constant names should use prefix \'C_\'.' % name)

		AddLocalIdentifier(name, stype, init, LineRef.FromString(line_num, line, name), filename, error, is_constant=True)

	return name_list, stype, init


def CheckForOthers(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]

	# only consider assignments, port maps, or initializations
	match = Match(r'.*(<=|:=|=>)\s*([xX]?\"0+\")', line)
	if match:
		error(filename, LineRef(line_num, match.start(2), match.end(2)), 'readability/others', 1, 'Use \'(others=>\'0\')\' instead of \'%s\'' % match.group(2))

	match = Match(r'.*(<=|:=|=>)\s*([xX]\"F+\")', line)
	if match:
		error(filename, LineRef(line_num, match.start(2), match.end(2)), 'readability/others', 1, 'Use \'(others=>\'1\')\' instead of \'%s\'' % match.group(2))

	match = Match(r'.*(<=|:=|=>)\s*[^xX](\"1+\")', line)
	if match:
		error(filename, LineRef(line_num, match.start(2), match.end(2)), 'readability/others', 1, 'Use \'(others=>\'1\')\' instead of \'%s\'' % match.group(2))


def CheckTimeUnits(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	matches = re.findall(r'.*\b((\d+)(ps|ns|us|ms|sec|min|hr))', line)
	for match in matches:
		orig = match[0]
		val = match[1]
		units = match[2]
		error(filename, LineRef.FromString(line_num, line, orig), 'readability/units', 2, 'Missing space before time units. Use \'%s %s\' instead of \'%s\'' % (val, units, orig))


def CheckReservedWords(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]
	# skip strings in quotes
	words = re.findall(r"[\"\'].*?[\"\']|(\w+)", line)
	# remove any reserved words
	words = [i for i in words if IsReservedWord(i)]
	for w in words:
		if not w.islower():
			error(filename, LineRef.FromString(line_num, line, w), 'readability/reserved', 2, 'Invalid capitalization on \'%s\'. Reserved words should use all lower case.' % (w))


def CheckLatches(filename, clean_lines, line_num, error):
	line = clean_lines.lines[line_num]

	# check for statements of the form
	# XXX <= YYY when ZZZ;
	match = Match(r'.*?\b\w+\b\s*<=\s*.*?\bwhen\b((?!\belse\b).)*;', line)
	if match:
		error(filename, LineRef.OnlyLine(line_num), 'runtime/latches', 5, 'Inferred latch detected. Output must be defined for all branch paths.')


def CheckLineLength(filename, clean_lines, line_num, error):
	line = clean_lines.raw_lines[line_num]
	if _line_length > 0:
		if len(line) > _line_length:
			error(filename, LineRef.OnlyLine(line_num), 'whitespace/line_length', 2, 'Line length is %i characters. Lines should be <= %i characters long' % (len(line), _line_length))


def CheckUnusedIdentifiers(filename, error):
	for v in _all_identifiers.keys():
		if IsIdentifierWithType(v):
			i = GetIdentifierWithType(v)
		elif IsReferencedIdentifier(v):
			i = GetIdentifier(v)
		else:
			continue

		# check if the item is not referenced anywhere
		if not i.IsReferenced():
			error(filename, i.lineref, 'build/unused', 2, 'Unused identifier \'%s\'.' % (i.Name()))


def ProcessLine(filename, file_extension, clean_lines, line, error, extra_check_functions=None):
	"""Processes a single line in the file.
	Args:
		filename: Filename of the file that is being processed.
		file_extension: The extension (dot not included) of the file.
		clean_lines: An array of strings, each representing a line of the file,
								 with comments stripped.
		line: Number of line being processed.
		include_state: An _IncludeState instance in which the headers are inserted.
		function_state: A _FunctionState instance which counts function lines, etc.
		nesting_state: A NestingState instance which maintains information about
									 the current stack of nested blocks being parsed.
		error: A callable to which errors are reported, which takes 4 arguments:
					 filename, line number, error level, and message
		extra_check_functions: An array of additional check functions that will be
													 run on each source line. Each function takes 4
													 arguments: filename, clean_lines, line, error
	"""
	raw_lines = clean_lines.raw_lines
	CheckStyle(filename, clean_lines, line, file_extension, error)
	CheckUsedPackages(filename, clean_lines, line, error)
	CheckEntities(filename, clean_lines, line, error)
	CheckArchitectures(filename, clean_lines, line, error)
	CheckPackages(filename, clean_lines, line, error)
	CheckPackageBodies(filename, clean_lines, line, error)
	CheckLineLength(filename, clean_lines, line, error)
	CheckForOthers(filename, clean_lines, line, error)
	CheckTimeUnits(filename, clean_lines, line, error)
	CheckReservedWords(filename, clean_lines, line, error)
	CheckLatches(filename, clean_lines, line, error)
	CheckBooleans(filename, clean_lines, line, error)
	CheckComment(raw_lines[line], filename, line, error)
	if extra_check_functions:
		for check_fn in extra_check_functions:
			check_fn(filename, clean_lines, line, error)


def ProcessFileData(filename, file_extension, lines, error, extra_check_functions=None):
	"""Performs lint checks and reports any errors to the given error function.
	Args:
		filename: Filename of the file that is being processed.
		file_extension: The extension (dot not included) of the file.
		lines: An array of strings, each representing a line of the file, with the
					 last element being empty if the file is terminated with a newline.
		error: A callable to which errors are reported, which takes 4 arguments:
					 filename, line number, error level, and message
		extra_check_functions: An array of additional check functions that will be
							 run on each source line. Each function takes 4
							 arguments: filename, clean_lines, line, error
	"""
	lines = (['// marker so line numbers and indices both start at 1'] + lines +
			['// marker so line numbers end in a known way'])

	ResetNolintSuppressions()
	ResetFileData()
	CheckForHeader(filename, lines, error)
	CheckForCopyright(filename, lines, error)
	ProcessGlobalSuppresions(lines)
	RemoveMultiLineComments(filename, lines, error)
	clean_lines = CleansedLines(lines)

	for line in xrange(clean_lines.NumLines()):
		ParseNolintSuppressions(filename, clean_lines.raw_lines[line], line, error)

	for line in xrange(clean_lines.NumLines()):
		ProcessLine(filename, file_extension, clean_lines, line, error, extra_check_functions)

	CheckUnusedIdentifiers(filename, error)

	# We check here rather than inside ProcessLine so that we see raw
	# lines rather than "cleaned" lines.
	CheckForBadCharacters(filename, lines, error)
	CheckForNewlineAtEOF(filename, lines, error)


def ProcessConfigOverrides(filename):
	""" Loads the configuration files and processes the config overrides.
	Args:
		filename: The name of the file being processed by the linter.
	Returns:
		False if the current |filename| should not be processed further.
	"""

	abs_filename = os.path.abspath(filename)
	cfg_filters = []
	keep_looking = True
	base_name = None
	while keep_looking:
		abs_path, bn = os.path.split(abs_filename)
		if not bn:
			break  # Reached the root directory.
		if base_name:
			base_name = os.path.join(bn, base_name)
		else:
			base_name = bn
		cfg_file = os.path.join(abs_path, "VHDLLINT.cfg")
		abs_filename = abs_path
		if not os.path.isfile(cfg_file):
			continue

		try:
			with open(cfg_file) as file_handle:
				for line in file_handle:
					line, _, _ = line.partition('#')  # Remove comments.
					if not line.strip():
						continue

					name, _, val = line.partition('=')
					name = name.strip()
					val = val.strip()
					if name == 'set noparent':
						keep_looking = False
					elif name == 'filter':
						cfg_filters.append(val)
					elif name == 'exclude_files':
						# When matching exclude_files pattern, use the base_name of
						# the current file name or the directory name we are processing.
						# For example, if we are checking for lint errors in /foo/bar/baz.cc
						# and we found the .cfg file at /foo/VHDLLINT.cfg, then the config
						# file's "exclude_files" filter is meant to be checked against "bar"
						# and not "baz" nor "bar/baz.cc".
						if base_name:
							# Convert to path and back to get the right slashes
							val = str(Path(f'{val}'))
							pattern = re.compile(re.escape(val))
							if pattern.match(base_name):
								if _lint_state.quiet:
									# Suppress "Ignoring file" warning when using --quiet.
									return False
								_lint_state.PrintInfo('Ignoring "%s": file excluded by "%s". '
																 'File path component "%s" matches '
																 'pattern "%s"\n' %
																 (filename, cfg_file, base_name, val))
								return False
					elif name == 'linelength':
						global _line_length
						try:
							_line_length = int(val)
						except ValueError:
							_lint_state.PrintError('Line length must be numeric.')
					elif name == 'extensions':
						ProcessExtensionsOption(val)
					elif name == 'root':
						global _root
						# root directories are specified relative to VHDLLINT.cfg dir.
						_root = os.path.join(os.path.dirname(cfg_file), val)
					else:
						_lint_state.PrintError(
								'Invalid configuration option (%s) in file %s\n' %
								(name, cfg_file))

		except IOError:
			_lint_state.PrintError(
					"Skipping config file '%s': Can't open for reading\n" % cfg_file)
			keep_looking = False

	# Apply all the accumulated filters in reverse order (top-level directory
	# config options having the least priority).
	for cfg_filter in reversed(cfg_filters):
		_AddFilters(cfg_filter)

	return True


def ProcessFile(filename, vlevel, extra_check_functions=None):
	"""Does google-lint on a single file.
	Args:
		filename: The name of the file to parse.
		vlevel: The level of errors to report.	Every error of confidence
		>= verbose_level will be reported.	0 is a good default.
		extra_check_functions: An array of additional check functions that will be
													 run on each source line. Each function takes 4
													 arguments: filename, clean_lines, line, error
	"""

	_SetVerboseLevel(vlevel)
	_BackupFilters()
	old_errors = _lint_state.error_count

	if not ProcessConfigOverrides(filename):
		_RestoreFilters()
		return
	_lint_state.PrintVerbose("processing file %s\n" % filename)

	lf_lines = []
	crlf_lines = []
	try:
		# Support the UNIX convention of using "-" for stdin.	Note that
		# we are not opening the file with universal newline support
		# (which codecs doesn't support anyway), so the resulting lines do
		# contain trailing '\r' characters if we are reading a file that
		# has CRLF endings.
		# If after the split a trailing '\r' is present, it is removed
		# below.
		if filename == '-':
			lines = codecs.StreamReaderWriter(sys.stdin,
											codecs.getreader('utf8'),
											codecs.getwriter('utf8'),
											'replace').read().split('\n')
		else:
			with codecs.open(filename, 'r', 'utf8', 'replace') as target_file:
				lines = target_file.read().split('\n')

		# Remove trailing '\r'.
		# The -1 accounts for the extra trailing blank line we get from split()
		for linenum in range(len(lines) - 1):
			if lines[linenum].endswith('\r'):
				lines[linenum] = lines[linenum].rstrip('\r')
				crlf_lines.append(linenum + 1)
			else:
				lf_lines.append(linenum + 1)

	except IOError:
		_lint_state.PrintError(
				"Skipping input '%s': Can't open for reading\n" % filename)
		_RestoreFilters()
		return

	# Note, if no dot is found, this will give the entire filename as the ext.
	file_extension = filename[filename.rfind('.') + 1:]

	# When reading from stdin, the extension is unknown, so no vhdllint tests
	# should rely on the extension.
	if filename != '-' and file_extension not in GetAllExtensions():
		_lint_state.PrintError('Ignoring %s; not a valid file name '
										 '(%s)\n' % (filename, ', '.join(GetAllExtensions())))
	else:
		ProcessFileData(filename, file_extension, lines, Error, extra_check_functions)

		# If end-of-line sequences are a mix of LF and CR-LF, issue
		# warnings on the lines with CR.
		#
		# Don't issue any warnings if all lines are uniformly LF or CR-LF,
		# since critique can handle these just fine, and the style guide
		# doesn't dictate a particular end of line sequence.
		#
		# We can't depend on os.linesep to determine what the desired
		# end-of-line sequence should be, since that will return the
		# server-side end-of-line sequence.
		if lf_lines and crlf_lines:
			# Warn on every line with CR.	An alternative approach might be to
			# check whether the file is mostly CRLF or just LF, and warn on the
			# minority, we bias toward LF here since most tools prefer LF.
			for linenum in crlf_lines:
				Error(filename, LineRef.OnlyLine(linenum), 'whitespace/newline', 1,
							'Unexpected \\r (^M) found; better to use only \\n')

	# Suppress printing anything if --quiet was passed unless the error
	# count has increased after processing this file.
	if not _lint_state.quiet or old_errors != _lint_state.error_count:
		_lint_state.PrintInfo('Done processing %s\n' % filename)
	_RestoreFilters()


def ParseArguments(args):
	try:
		(opts, filenames) = getopt.getopt(args, '', ['help', 'output=', 'verbose=',
                                                 'v=',
                                                 'version',
                                                 'counting=',
                                                 'filter=',
                                                 'root=',
                                                 'repository=',
                                                 'linelength=',
                                                 'extensions=',
                                                 'exclude=',
                                                 'recursive',
                                                 'quiet'])
	except getopt.GetoptError:
		PrintUsage('Invalid arguments.')

	verbosity = _VerboseLevel()
	output_format = _OutputFormat()
	filters = ''
	quiet = _Quiet()
	counting_style = ''
	recursive = False

	for (opt, val) in opts:
		if opt == '--help':
			PrintUsage(None)
		if opt == '--version':
			PrintVersion()
		elif opt == '--output':
			if val not in ('emacs', 'vs7', 'eclipse', 'junit', 'sed', 'gsed'):
				PrintUsage('The only allowed output formats are emacs, vs7, eclipse '
									 'sed, gsed and junit.')
			output_format = val
		elif opt == '--quiet':
			quiet = True
		elif opt == '--verbose' or opt == '--v':
			verbosity = int(val)
		elif opt == '--filter':
			filters = val
			if not filters:
				PrintCategories()
		elif opt == '--counting':
			if val not in ('total', 'toplevel', 'detailed'):
				PrintUsage('Valid counting options are total, toplevel, and detailed')
			counting_style = val
		elif opt == '--root':
			global _root
			_root = val
		elif opt == '--repository':
			global _repository
			_repository = val
		elif opt == '--linelength':
			global _line_length
			try:
				_line_length = int(val)
			except ValueError:
				PrintUsage('Line length must be digits.')
		elif opt == '--exclude':
			global _excludes
			if not _excludes:
				_excludes = set()
			_excludes.update(glob.glob(val, recursive=True))
		elif opt == '--extensions':
			ProcessExtensionsOption(val)
		elif opt == '--recursive':
			recursive = True

	if not filenames:
		PrintUsage('No files were specified.')

	if recursive:
		filenames = _ExpandDirectories(filenames)

	if _excludes:
		filenames = _FilterExcludedFiles(filenames)

	_SetOutputFormat(output_format)
	_SetQuiet(quiet)
	_SetVerboseLevel(verbosity)
	_SetFilters(filters)
	_SetCountingStyle(counting_style)

	filenames.sort()
	return filenames


def _ExpandDirectories(filenames):
	"""Searches a list of filenames and replaces directories in the list with
	all files descending from those directories. Files with extensions not in
	the valid extensions list are excluded.
	Args:
		filenames: A list of files or directories
	Returns:
		A list of all files that are members of filenames or descended from a
		directory in filenames
	"""
	expanded = set()
	for filename in filenames:
		if not os.path.isdir(filename):
			expanded.add(filename)
			continue

		for root, _, files in os.walk(filename):
			for loopfile in files:
				fullname = os.path.join(root, loopfile)
				if fullname.startswith('.' + os.path.sep):
					fullname = fullname[len('.' + os.path.sep):]
				expanded.add(fullname)

	filtered = []
	for filename in expanded:
		if os.path.splitext(filename)[1][1:] in GetAllExtensions():
			filtered.append(filename)
	return filtered


def _FilterExcludedFiles(fnames):
	"""Filters out files listed in the --exclude command line switch. File paths
	in the switch are evaluated relative to the current working directory
	"""
	exclude_paths = [os.path.abspath(f) for f in _excludes]
	# because globbing does not work recursively, exclude all subpath of all excluded entries
	return [f for f in fnames
					if not any(e for e in exclude_paths
									if _IsParentOrSame(e, os.path.abspath(f)))]


def _IsParentOrSame(parent, child):
	"""Return true if child is subdirectory of parent.
	Assumes both paths are absolute and don't contain symlinks.
	"""
	parent = os.path.normpath(parent)
	child = os.path.normpath(child)
	if parent == child:
		return True

	prefix = os.path.commonprefix([parent, child])
	if prefix != parent:
		return False
	# Note: os.path.commonprefix operates on character basis, so
	# take extra care of situations like '/foo/ba' and '/foo/bar/baz'
	child_suffix = child[len(prefix):]
	child_suffix = child_suffix.lstrip(os.sep)
	return child == os.path.join(prefix, child_suffix)


def main():
	filenames = ParseArguments(sys.argv[1:])
	backup_err = sys.stderr
	try:
		# Change stderr to write with replacement characters so we don't die
		# if we try to print something containing non-ASCII characters.
		sys.stderr = codecs.StreamReader(sys.stderr, 'replace')

		_lint_state.ResetErrorCounts()
		for filename in filenames:
			ProcessFile(filename, _lint_state.verbose_level)
		# If --quiet is passed, suppress printing error count unless there are errors.
		if not _lint_state.quiet or _lint_state.error_count > 0:
			_lint_state.PrintErrorCounts()

		if _lint_state.output_format == 'junit':
			sys.stderr.write(_lint_state.FormatJUnitXML())

	finally:
		sys.stderr = backup_err

	sys.exit(_lint_state.error_count > 0)


if __name__ == '__main__':
	main()
