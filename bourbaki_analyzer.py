import sys
import re
import os

TARGETS = [
    "isSimple",
    "patch_boundary_has_convex_corner",
    "generateRules_stitch_check",
    "generateRules_dir_match",
    "rule_dir_match",
    "boundary_path_length_ge",
    "peel_patch_singleton_spliced",
    "peel_patch_singleton_remainder",
    "peel_patch_general_spliced",
    "peel_patch_general_remainder",
    "peel_patch",
    "peelBoundary"
]

def get_blocks(file_content):
    lines = file_content.splitlines()
    blocks = {}
    decl_pattern = re.compile(r'^\s*(?:noncomputable\s+)?(?:def|theorem|lemma)\s+(\w+)')
    
    decl_starts = []
    for idx, line in enumerate(lines):
        match = decl_pattern.match(line)
        if match:
            name = match.group(1)
            decl_starts.append((name, idx))
            
    for target in TARGETS:
        start_idx = None
        for name, idx in decl_starts:
            if name == target:
                start_idx = idx
                break
        if start_idx is None:
            # Fallback: scan for any line declaring target
            for idx, line in enumerate(lines):
                if target in line and ('def ' in line or 'theorem ' in line or 'lemma ' in line):
                    start_idx = idx
                    break
        if start_idx is not None:
            end_idx = len(lines)
            for name, idx in decl_starts:
                if idx > start_idx:
                    end_idx = idx
                    break
            blocks[target] = lines[start_idx:end_idx]
    return blocks

def analyze_block(block_lines):
    content = "\n".join(block_lines)
    block_len = len(block_lines)
    if block_len == 0:
        return 0.0, 0.0, 0.0, 0.0
        
    have_count = len(re.findall(r'\bhave\b', content))
    let_count = len(re.findall(r'\blet\b', content))
    hl_count = have_count + let_count
    
    sorry_count = len(re.findall(r'\bsorry\b', content))
    
    H = 1.0 / (1.0 + hl_count)
    Lambda = sorry_count / block_len
    S = hl_count / block_len
    U = (1.0 - Lambda) * (1.0 - H)
    
    return H, Lambda, S, U

def render_plot(values):
    steps = ["HEAD~9", "HEAD~8", "HEAD~7", "HEAD~6", "HEAD~5", "HEAD~4", "HEAD~3", "HEAD~2", "HEAD~1", "HEAD~0"]
    min_v = min(values)
    max_v = max(values)
    if max_v == min_v:
        max_v += 0.1
        min_v -= 0.1
    span = max_v - min_v
    
    height = 10
    width = len(values)
    
    lines = []
    lines.append("Global Mesh Stability Index Trajectory (HEAD~9 -> HEAD~0):")
    lines.append("-" * 75)
    for r in range(height - 1, -1, -1):
        row_val = min_v + (r / (height - 1)) * span
        row_str = f"{row_val:.4f} | "
        for idx, val in enumerate(values):
            expected_row = int(round(((val - min_v) / span) * (height - 1)))
            if expected_row == r:
                row_str += "   *    "
            else:
                row_str += "        "
        lines.append(row_str)
    lines.append("       |" + "--------" * width)
    x_axis_labels = "         " + " ".join(f"{s:<7}" for s in steps)
    lines.append(x_axis_labels)
    lines.append("-" * 75)
    return "\n".join(lines)

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 bourbaki_analyzer.py <file_path_or_data_path> [--raw] [--plot]")
        sys.exit(1)
        
    path = sys.argv[1]
    raw_mode = "--raw" in sys.argv
    plot_mode = "--plot" in sys.argv
    
    if plot_mode:
        if not os.path.exists(path):
            print(f"Error: Data file {path} not found.")
            sys.exit(1)
        with open(path, 'r') as f:
            lines = f.read().splitlines()
        values = []
        for line in lines:
            if line.strip():
                try:
                    values.append(float(line.strip()))
                except ValueError:
                    pass
        if len(values) < 10:
            print(f"Warning: Expected at least 10 values in history, got {len(values)}.")
        # history.dat is populated from HEAD~0 to HEAD~9, so reverse it to make it chronological
        values = list(reversed(values))
        print(render_plot(values))
        sys.exit(0)
        
    if not os.path.exists(path):
        print(f"Error: File {path} not found.")
        sys.exit(1)
        
    with open(path, 'r') as f:
        content = f.read()
        
    blocks = get_blocks(content)
    
    hardening_indices = []
    report_lines = []
    
    report_lines.append("| Target Declaration | Entropy (H) | Leaf Density (Λ) | Saturation (S) | Hardening Index (U) |")
    report_lines.append("|---|---|---|---|---|")
    
    for target in TARGETS:
        block = blocks.get(target, [])
        H, Lambda, S, U = analyze_block(block)
        hardening_indices.append(U)
        report_lines.append(f"| `{target}` | {H:.4f} | {Lambda:.4f} | {S:.4f} | {U:.4f} |")
        
    # Global Mesh Stability Index is the average of hardening indices
    global_stability = sum(hardening_indices) / len(hardening_indices) if hardening_indices else 0.0
    
    if raw_mode:
        print(f"{global_stability:.6f}")
    else:
        print("Bourbaki Proof Mesh Analysis Report")
        print("===================================")
        print("\n".join(report_lines))
        print(f"\nGlobal Mesh Stability Index: {global_stability:.6f}")

if __name__ == "__main__":
    main()
