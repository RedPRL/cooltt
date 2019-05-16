#!/bin/bash

for file in test/*.blott; do
  echo "Checking ${file}"
  dune exec blott -- $file
  echo $'' # print newline ???
done

echo DONE
