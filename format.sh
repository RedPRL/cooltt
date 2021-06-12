#!/bin/bash
git --no-pager diff origin/main --name-only | grep -E ".*\.ml(i)?$" | xargs -I% ocp-indent -i %
