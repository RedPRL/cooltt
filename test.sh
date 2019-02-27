#!/bin/bash

for file in test/*; do
  echo "Checking ${file}"
  dune exec blott -- $file || exit 1
  echo $'' # print newline ???
done

echo DONE
