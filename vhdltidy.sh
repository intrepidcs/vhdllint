#!/bin/bash

# now "$@" is the list of input files.

ENABLE_CRLF_TO_LF=0
ENABLE_COMMENT_WS=1
ENABLE_REMOVE_TRAILING_WS=1
ENABLE_REMOVE_LEADING_BLANKS=1
ENABLE_REMOVE_TRAILING_BLANKS=1
ENABLE_REMOVE_CONSECUTIVE_BLANKS=1
ENABLE_SIMPLIFY_BOOLEANS=0
ENABLE_TIME_UNIT_WS=1
ENABLE_CONVERT_RISING_EDGE=1

for file in "$@"; do

  if [ ! -f "$file" ]; then
    echo "File $file does not exist!"
  fi
  
  echo "Processing file $file..."
  
  # convert to unix line endings
  if [ $ENABLE_CRLF_TO_LF -ne 0 ]; then
    sed -i 's/\r//' "$file"
  fi
  
  # make sure there is at least 1 space after comments "--"
  if [ $ENABLE_COMMENT_WS -ne 0 ]; then
    sed -i 's/--\([^-= ].*\)$/-- \1/' "$file"
  fi
  
  # delete trailing whitespace (spaces, tabs) from end of each line
  if [ $ENABLE_REMOVE_TRAILING_WS -ne 0 ]; then
    sed -i 's/[ \t]*\(\r\?\)$/\1/' "$file"
  fi
  
  # delete all leading blank lines at top of file
  if [ $ENABLE_REMOVE_LEADING_BLANKS -ne 0 ]; then
    sed -i '/[^\s\r]/,$!d' "$file"
  fi
  
  # Delete all trailing blank lines at end of file (only).
  if [ $ENABLE_REMOVE_TRAILING_BLANKS -ne 0 ]; then
    sed -i ':a;/^[ \r\n]*$/{$d;N;ba}' "$file"
  fi
  
  # Remove 3 or more consectutive blank lines
  # and replace with 2 blank lines
  if [ $ENABLE_REMOVE_CONSECUTIVE_BLANKS -ne 0 ]; then
    sed -i  '/^[ \t\r]*$/N;/\r\n\r$/N;//D' "$file" # works with CRLF
    sed -i  '/^[ \t\r]*$/N;/\n$/N;//D' "$file" # works with LF
  fi
  
  # simplify boolean expressions
  # replace 'XXX = true' with 'XXX'
  # replace 'true = XXX' with 'XXX'
  if [ $ENABLE_SIMPLIFY_BOOLEANS -ne 0 ]; then
    sed -i 's/\s*=\s*\<true\>//i' "$file"
    sed -i 's/\<true\>\s*=\s*//i' "$file"
  fi
  
  # Add space to time units
  if [ $ENABLE_TIME_UNIT_WS -ne 0 ]; then
    sed -i 's/\b\([0-9][0-9]*\)\(ps\|ns\|us\|ms\|sec\|min\|hr\)\b/\1 \2/i' "$file"
  fi
  
  # replace "clk'event and clk = '1'" with rising_edge(clk)
  # replace "clk'event and clk = '0'" with falling_edge(clk)
  if [ $ENABLE_CONVERT_RISING_EDGE -ne 0 ]; then
    sed -i 's/\b\([a-zA-Z0-9_]*\)'\''event \s*and \s*\1 \s*= \s*'\''1'\''/rising_edge(\1)/i' "$file"
    sed -i 's/\b\([a-zA-Z0-9_]*\)'\''event \s*and \s*\1 \s*= \s*'\''0'\''/falling_edge(\1)/i' "$file"
  fi
  
  # make sure all reserved words are lowercase
  #KEYWORD_REPLACE="s/\<all\>/all/gi"
  #sed -i  $KEYWORD_REPLACE "$file"
  
  echo "Done processing file $file."
  
done
