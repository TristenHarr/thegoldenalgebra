import os

# --- Configuration ---
ROOT_DIRECTORY = '.'  # Current directory
OUTPUT_FILE = 'ai_bundle.tex'
EXCLUDE_DIRS = {'build', '.git', 'applications'} # Add any other directories to ignore
INCLUDE_EXTENSIONS = {'.tex'}

def bundle_project():
    """
    Traverses the project directory and bundles all specified text-based files
    into a single output file with headers indicating the original file path.
    """
    print(f"Starting to bundle project from '{ROOT_DIRECTORY}'...")
    
    # Use a list to build the content efficiently
    bundle_content = []
    
    # os.walk is perfect for traversing the directory tree
    for dirpath, dirnames, filenames in os.walk(ROOT_DIRECTORY, topdown=True):
        # Modify dirnames in-place to prevent os.walk from descending into excluded directories
        dirnames[:] = [d for d in dirnames if d not in EXCLUDE_DIRS]
        
        for filename in sorted(filenames):
            # Check if the file has one of the desired extensions
            if any(filename.endswith(ext) for ext in INCLUDE_EXTENSIONS):
                file_path = os.path.join(dirpath, filename)
                
                # Use forward slashes for cross-platform consistency in the bundle
                relative_path = file_path.replace(os.path.sep, '/').lstrip('./')
                
                print(f"  -> Adding file: {relative_path}")
                
                # Create a clear header for each file
                header = f"\n%======================================================================\n" \
                         f"% FILE: {relative_path}\n" \
                         f"%======================================================================\n\n"
                
                bundle_content.append(header)
                
                # Read the content of the file and append it
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        bundle_content.append(f.read())
                    bundle_content.append('\n')
                except Exception as e:
                    bundle_content.append(f"% ERROR READING FILE: {e}\n")

    # Write the collected content to the output file
    try:
        with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
            f.write("".join(bundle_content))
        print(f"\nSuccess! Project bundled into '{OUTPUT_FILE}'")
    except Exception as e:
        print(f"\nError writing to output file: {e}")

if __name__ == '__main__':
    bundle_project()