#! /opt/homebrew/bin/fish

set fileToParse (ls **/$argv[1])[1]
set outputFile (echo $fileToParse | cut -f 1 -d '.').output
set langSpecDir (dirname (dirname (dirname (ls **/$argv[1]))))
set langSpec (ls *$langSpecDir/*.syl)[1]

cargo build --release;
and ./target/release/sylver parse --spec $langSpec --file $fileToParse > $outputFile
