#!/usr/bin/env bash

# First arg (optional) is filter
filter=$1

# List files (tests/*.gil)
is_first=true
for file in tests/*.gil; do
    if [ -n "$filter" ] && [[ ! $file =~ $filter ]]; then
        continue
    fi

    if $is_first; then
        is_first=false
    else
        w=$(tput cols)
        printf "\n%*s\n\n" $w | tr " " "="
    fi

    echo "Processing $file"

    # Get model in first line, formatted as "(* <model> *)"
    first_line=$(head -n 1 $file)
    model=$(echo $first_line | sed -n 's/(\* \(.*\) \*)/\1/p')
    echo "Using model $model"

    # Replace line "module MyMem = ..." with "module MyMem = <model>" in ../bin/main.ml
    sed -i '' "s/module MyMem = .*/module MyMem = $model/" bin/main.ml

    # Compile, run
    esy build 2>&1 > /dev/null
    esy x instantiation verify -a -ltmi "$file"
done
