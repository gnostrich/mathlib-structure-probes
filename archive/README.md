**Structure-First Backpropagation**

This repo explores a simple training rule:

Train a dense directed graph spanning inputs and outputs with standard backprop, and interleave discrete rounding steps that snap all weights to {0, 1}.

The graph’s structure is learned during training, not fixed in advance.

**The Setup**

We start with a dense directed graph.

The node set includes:

input nodes (I),

output nodes (O),

optional internal nodes.

Directed edges are allowed between nodes at the chosen granularity.

There is no predefined architecture unless you impose one.

**Parameters**

All parameters are weights.

Weights may live:

on directed edges,

on nodes (self-weights / gates).

There is no semantic distinction between node weights and edge weights.

If a weight is zero, the corresponding connection or node is inactive.

---

## Repository Structure

This repository contains versioned implementations to track iterations and improvements:

- **`v1/`** - Initial implementation (current)
  - PyTorch prototype with architecture diagrams and pseudocode
  - Demonstrations on XOR and addition tasks
  - See [v1/README.md](v1/README.md) for details

Future versions (v2, v3, etc.) will be added as separate directories with their own documentation.

## Quick Start (v1)

```bash
cd v1
pip install -r requirements.txt
python example.py
```

See the [v1 directory](v1/) for the complete implementation and documentation.
