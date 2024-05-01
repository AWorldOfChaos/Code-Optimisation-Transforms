#!/bin/bash

# Define the paths to the folders containing the Test.class files
folder_a="./sootOutput/"
folder_b="./testcase/"

# Function to run Test.class file 1000 times and measure time
run_tests() {
    local folder=$1
    local total_time=0

    for (( i=1; i<=100; i++ )); do
        start=$(date +%s%N)
        java -Xint -cp $folder Test >/dev/null
        end=$(date +%s%N)
        runtime=$((end-start))
        total_time=$((total_time+runtime))
    done

    avg_time=$((total_time/1000))
    echo "Average runtime for tests in $folder: $avg_time nanoseconds"
}

# Run tests for folder a
echo "Running tests for folder a..."
run_tests "$folder_a"

# Run tests for folder b
echo "Running tests for folder b..."
run_tests "$folder_b"
