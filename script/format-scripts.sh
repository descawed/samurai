#!/usr/bin/env bash
set -u

if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
    echo "Usage: $0 <input_folder> <output_folder> [encoding]" >&2
    exit 1
fi

input_folder=${1%/}
output_folder=${2%/}
encoding=${3:-'shift-jis'}

if [ ! -d "$input_folder" ]; then
    echo "Input folder does not exist: $input_folder" >&2
    exit 1
fi

mkdir -p "$output_folder"

while IFS= read -r -d '' input_path; do
    rel_path=${input_path#"$input_folder"/}
    output_path=$output_folder/$rel_path
    mkdir -p "$(dirname "$output_path")"

    case $(basename "$input_path") in
        config.h|assign.h|scriptmessage.h)
            # using advanced formatting for config.h causes recursive variable definitions, and assign.h and
            # scriptmessage.h are not regular scripts and contain syntax errors
            if ! samurai script format -t 4 -e "$encoding" -s "$input_path" "$output_path"; then
              echo "Failed to format: $input_path" >&2
            fi
            ;;
        *.sol|*.lst|*.h)
            if ! samurai script format -t 4 -c "$input_folder/config.h" -e "$encoding" -q "$input_path" "$output_path"; then
                echo "Failed to format: $input_path; trying simple format" >&2
                if ! samurai script format -t 4 -e "$encoding" -s "$input_path" "$output_path"; then
                  echo "Simple format failed: $input_path" >&2
                fi
            fi
            ;;
        *)
            cp -f "$input_path" "$output_path"
            ;;
    esac
done < <(find "$input_folder" -type f -print0)
