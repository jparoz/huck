#!/usr/bin/env bash

for FILE in "$@"
do
    if [[ ! -s "$FILE" ]]
    then
        echo $FILE is empty!
        exit 1
    fi
done
