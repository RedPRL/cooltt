#!/bin/bash
git ls-files | grep -E ".*\.ml(i)?$" | xargs -I% bash -c 'ocp-indent -i %'

