#!/bin/bash

for file in test/*.cooltt; do
  echo "Checking ${file}"
  dune exec cooltt -- $file || exit 1
  echo $'' # print newline ???
done

echo DONE
