#!/bin/bash

for file in test/*.funtt; do
  echo "Checking ${file}"
  dune exec funtt -- $file
  echo $'' # print newline ???
done

echo DONE
