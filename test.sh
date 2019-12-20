#!/bin/bash

for file in test/*.cooltt; do
  echo "Checking ${file}"
  dune exec cooltt -- $file
  echo $'' # print newline ???
done

echo DONE
