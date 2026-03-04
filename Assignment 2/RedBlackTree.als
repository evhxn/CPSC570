/*
 * Red-Black Tree Specification in Alloy
 * CPSC 570: From Bugs to Proofs — Assignment 2, Exercise 3
 *
 * A red-black tree is a binary search tree with the following properties:
 *   1. Every node is either red or black.
 *   2. The root is black.
 *   3. Every leaf (NIL) is black.
 *   4. If a node is red, then both its children are black.
 *   5. For each node, all paths from that node to descendant NIL
 *      nodes pass through the same number of black nodes.
 *
 * The black-height property (5) uses the cardinality operator (#)
 * as suggested by the exercise. The Int scope is set to 4 bits
 * to handle counting without overflow.
 */

-- Signatures

abstract sig Color {}
one sig Red, Black extends Color {}

abstract sig Node {
    color: one Color
}

-- NIL sentinel leaves: always black, no children
sig NIL extends Node {} {
    color = Black
}

-- Internal nodes with left and right children
sig Internal extends Node {
    left:  one Node,
    right: one Node
}

-- Exactly one root
one sig Root in Internal {}


-- Helper: descendants and paths

-- All descendants reachable from a node (via left + right)
fun descendants[n: Node]: set Node {
    n.^(left + right)
}

-- All ancestors of a node (nodes that can reach n)
fun ancestors[n: Node]: set Internal {
    n.~^(left + right) & Internal
}

-- The set of nodes on the path from root to a given node (inclusive)
fun pathFromRoot[n: Node]: set Node {
    n.*(~(left + right)) & (Root + Root.^(left + right))
}

-- Count of black nodes on the path from root to n (inclusive)
fun blackCount[n: Node]: Int {
    #{x: pathFromRoot[n] | x.color = Black}
}


-- Facts: tree structure

fact ValidTree {
    -- All internal nodes (except Root) are reachable from Root
    Internal - Root in Root.^(left + right)

    -- All NIL nodes are reachable from Root
    NIL in Root.^(left + right)

    -- Acyclicity: no node is its own descendant
    all n: Internal | n not in descendants[n]

    -- Each non-root node has exactly one parent
    all n: (Internal + NIL) - Root | one p: Internal |
        n = p.left or n = p.right

    -- Root has no parent
    no p: Internal | Root = p.left or Root = p.right

    -- Left and right children of a node are distinct
    all n: Internal | n.left != n.right
}


-- Red-Black Properties

-- Property 2: Root is black
fact RootIsBlack {
    Root.color = Black
}

-- Property 4: Red nodes have black children
fact RedHasBlackChildren {
    all n: Internal | n.color = Red implies
        (n.left.color = Black and n.right.color = Black)
}

-- Property 5: Black-height property
-- For every internal node, all descendant NIL nodes have
-- the same black-count (number of black nodes on the path
-- from root to that NIL).
fact BlackHeightConsistent {
    all n: Internal | let nilsL = n.left.*(left + right) & NIL,
                          nilsR = n.right.*(left + right) & NIL |
        -- All left-subtree NILs have the same black count
        (all a, b: nilsL | blackCount[a] = blackCount[b]) and
        -- All right-subtree NILs have the same black count
        (all a, b: nilsR | blackCount[a] = blackCount[b]) and
        -- Left and right subtree NILs have the same black count
        (all a: nilsL, b: nilsR | blackCount[a] = blackCount[b])
}


-- Run commands: find interesting instances

-- A small tree with at least 3 internal nodes
run SmallTree {
    #Internal >= 3
} for exactly 4 Internal, exactly 5 NIL, 4 Int

-- A tree with some red nodes
run TreeWithRed {
    #Internal >= 3
    some n: Internal | n.color = Red
} for exactly 4 Internal, exactly 5 NIL, 4 Int

-- A larger tree
run BiggerTree {
    #Internal >= 5
    some n: Internal | n.color = Red
} for exactly 6 Internal, exactly 7 NIL, 4 Int

-- Minimal tree: just the root with two NIL children
run MinimalTree {} for exactly 1 Internal, exactly 2 NIL, 4 Int

-- Assertions

-- Red node's parent is always black
assert RedParentIsBlack {
    all r: Internal | r.color = Red implies
        all p: Internal | (r = p.left or r = p.right) implies
            p.color = Black
}
check RedParentIsBlack for 8 Node, 4 Int

-- All NIL leaves have the same black-count from root
assert AllLeavesEqualBlackDepth {
    all a, b: NIL | blackCount[a] = blackCount[b]
}
check AllLeavesEqualBlackDepth for 8 Node, 4 Int

-- The root is always black
assert RootBlack {
    Root.color = Black
}
check RootBlack for 8 Node, 4 Int
