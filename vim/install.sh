#!/bin/bash

DEST=~/.vim/pack/redprl-org/start ;
[ -d $DEST/vim-cooltt ] && rm -r $DEST/vim-cooltt ;
mkdir -p $DEST && cp -r . $DEST/vim-cooltt
