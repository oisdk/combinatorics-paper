#!/bin/bash
withcode=$1
nocode=${withcode#"agda/"}
cd agda || exit
agda --latex --latex-dir=. "$nocode"
