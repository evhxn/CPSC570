# Assignment 2: Red-Black Trees in Alloy

## Exercise 3: Red-Black Tree Specification

### How to Run

1. Open the **Alloy Analyzer** (version 6.x recommended)
2. File → Open → select `RedBlackTree.als`
3. In the Execute menu, choose one of the run commands:
   - **SmallTree** — 4 internal nodes, at least 3 required
   - **TreeWithRed** — tree with some red nodes
   - **BiggerTree** — 6 internal nodes with red nodes
   - **MinimalTree** — just root + 2 NIL children
4. Click **Show** to see the instance in the visualizer
5. Click **Next** to see alternative valid red-black trees

### Checking Assertions

From the Execute menu, run the `check` commands:
- **RedParentIsBlack** — verifies red nodes always have black parents
- **AllLeavesEqualBlackDepth** — verifies all NIL leaves have equal black depth
- **RootBlack** — verifies root is always black

All assertions should produce "No counterexample found."

### Customizing the Visualizer

To load the custom theme:
1. After showing an instance, click **Theme** in the visualizer
2. Click **Load** and select `RedBlackTree.thm`
3. The theme will:
   - Show left edges in blue (labeled "L") and right edges in red (labeled "R")
   - Hide the Color atoms (Red/Black sigs) to reduce clutter
   - Display NIL nodes as small black triangles
   - Display the Root as a black hexagon

Alternatively, you can manually customize:
1. Click on `Internal` → set color based on whether nodes are red/black
2. Hide the `color` relation edges (since color is shown on the nodes)
3. Set NIL nodes to a small dark shape

### Design Notes

- **NIL sentinels**: Modeled as explicit `NIL` signature nodes (always black), matching the standard red-black tree definition where leaves are NIL sentinels
- **Black-height property**: Uses the `#` (cardinality) operator to count black nodes on paths from root to each NIL, as suggested by the exercise. The `Int` scope is set to 4 bits to avoid overflow
- **Structure**: `Internal` nodes have `left` and `right` children; `Root` is a singleton subset of `Internal`

### Files

| File | Description |
|------|-------------|
| `RedBlackTree.als` | Alloy specification of Red-Black Trees |
| `RedBlackTree.thm` | Custom visualizer theme |
| `README.md` | This file |
