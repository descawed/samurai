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
        *.scc)
            cp -f "$input_path" "$output_path"
            ;;
        *)
            iconv -o "$output_path" -c -f WINDOWS-31J -t UTF-8//TRANSLIT "$input_path"
            ;;
    esac
done < <(find "$input_folder" -type f -print0)
