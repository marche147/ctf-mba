#!/bin/bash

cd `dirname ${BASH_SOURCE[0]}`
exec python3 -u ./server.py
