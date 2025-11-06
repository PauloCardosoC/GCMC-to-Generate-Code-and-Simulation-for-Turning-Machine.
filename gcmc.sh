#!/bin/bash

_CMD_GCMC="/usr/bin/gcmc"

${_CMD_GCMC} -q --svg-no-movelayer -G prologo.txt -P 5  $@
