#!/usr/bin/env bash
set -u

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <input_folder> <output_folder>" >&2
    exit 1
fi

input_folder=${1%/}
output_folder=${2%/}

if [ ! -d "$input_folder" ]; then
    echo "Input folder does not exist: $input_folder" >&2
    exit 1
fi

mkdir -p "$output_folder"

while IFS= read -r -d '' input_path; do
    rel_path=${input_path#"$input_folder"/}
    output_path=$output_folder/$rel_path
    mkdir -p "$(dirname "$output_path")"

    case "$input_path" in
        *.sol|*.lst)
            if ! samurai script format -t 4 -c "$input_folder/config.h" -e shift-jis -q "$input_path" "$output_path"; then
                echo "Failed to format: $input_path; trying simple format" >&2
                if ! samurai script format -t 4 -e shift-jis -s "$input_path" "$output_path"; then
                  echo "Simple format failed: $input_path" >&2
                fi
            fi
            ;;
        *)
            cp -f "$input_path" "$output_path"
            ;;
    esac
done < <(find "$input_folder" -type f -print0)
