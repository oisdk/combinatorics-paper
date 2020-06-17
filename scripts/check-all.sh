#!/usr/bin/env bash
( cd agda
echo '{-# OPTIONS --cubical --safe #-}
' > Everything
echo 'module Everything where
' >> Everything
find -E . -type f -regex '.*\.l?agda' | cut -c 3- | cut -f1 -d'.' | sed 's/\//\./g' | sed 's/^/open import /' >> Everything
mv Everything Everything.agda
agda --html --html-dir=../docs Everything.agda
rm Everything.agda
)
