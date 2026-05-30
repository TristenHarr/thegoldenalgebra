import os

# Set your source folder and output markdown file
source_folder = ".lake/packages/mathlib/MathLib/Analysis"
output_file = "output.md"

with open(output_file, "w", encoding="utf-8") as md_file:
    for root, _, files in os.walk(source_folder):
        for filename in sorted(files):
            if filename.endswith(".lean"):
                file_path = os.path.join(root, filename)
                rel_path = os.path.relpath(file_path, start=source_folder)

                md_file.write(f"{rel_path}:\n")
                md_file.write("```\n")
                with open(file_path, "r", encoding="utf-8") as py_file:
                    contents = py_file.read()
                    md_file.write(contents)
                md_file.write("\n```\n\n")

print(f"All Python files from '{source_folder}' have been written to '{output_file}'.")
