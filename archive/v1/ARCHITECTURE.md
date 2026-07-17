# Structure-First Backpropagation Architecture

## High-Level Architecture Diagram

```
┌────────────────────────────────────────────────────────────────────┐
│                   STRUCTURE-FIRST BACKPROP SYSTEM                   │
└────────────────────────────────────────────────────────────────────┘

INITIALIZATION PHASE:
┌─────────────────────────────────────────────────────────────────────┐
│  Dense Directed Graph                                               │
│  ┌──────────┐       ┌──────────┐       ┌──────────┐                │
│  │  Input   │       │ Hidden   │       │  Output  │                │
│  │  Node 1  │──────▶│  Node 1  │──────▶│  Node 1  │                │
│  │  (I₁)    │╲     ╱│  (H₁)    │╲     ╱│  (O₁)    │                │
│  └──────────┘ ╲   ╱ └──────────┘ ╲   ╱ └──────────┘                │
│                 ╲ ╱                ╲ ╱                              │
│  ┌──────────┐   ╳   ┌──────────┐   ╳   ┌──────────┐                │
│  │  Input   │  ╱ ╲  │ Hidden   │  ╱ ╲  │  Output  │                │
│  │  Node 2  │─────▶│  Node 2  │─────▶│  Node 2  │                │
│  │  (I₂)    │╱     ╲│  (H₂)    │╱     ╲│  (O₂)    │                │
│  └──────────┘       └──────────┘       └──────────┘                │
│                                                                     │
│  All edges initialized with continuous weights W ∈ ℝ               │
│  Fully connected: every possible edge exists initially             │
└─────────────────────────────────────────────────────────────────────┘

TRAINING LOOP (Alternating Phases):
┌─────────────────────────────────────────────────────────────────────┐
│  PHASE 1: STANDARD BACKPROPAGATION                                  │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  1. Forward Pass:                                           │   │
│  │     - Compute activations through graph                     │   │
│  │     - Use continuous weights W ∈ ℝ                          │   │
│  │                                                              │   │
│  │  2. Loss Computation:                                       │   │
│  │     - L(ŷ, y) = task-specific loss                          │   │
│  │                                                              │   │
│  │  3. Backward Pass:                                          │   │
│  │     - Compute gradients ∂L/∂W                               │   │
│  │                                                              │   │
│  │  4. Weight Update:                                          │   │
│  │     - W ← W - η∂L/∂W  (standard SGD/Adam)                   │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              ▼                                      │
│  PHASE 2: DISCRETE ROUNDING                                         │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  5. Structure Discretization:                               │   │
│  │     - W̃ ← round(W) = {0 if |W| < threshold, 1 otherwise}    │   │
│  │     - Or: W̃ ← {0 if W < 0.5, 1 if W ≥ 0.5}                  │   │
│  │                                                              │   │
│  │  6. Graph Pruning Effect:                                   │   │
│  │     - Edges with W̃ = 0 become inactive                      │   │
│  │     - Only W̃ = 1 edges remain in structure                  │   │
│  └─────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────┘

LEARNED STRUCTURE (After Training):
┌─────────────────────────────────────────────────────────────────────┐
│  Sparse Directed Graph (Structure Emerged from Training)            │
│  ┌──────────┐                       ┌──────────┐                    │
│  │  Input   │                       │  Output  │                    │
│  │  Node 1  │──────────────────────▶│  Node 1  │                    │
│  │  (I₁)    │                       │  (O₁)    │                    │
│  └──────────┘                       └──────────┘                    │
│                                         ▲                            │
│                                         │                            │
│  ┌──────────┐       ┌──────────┐       │                            │
│  │  Input   │       │ Hidden   │       │                            │
│  │  Node 2  │──────▶│  Node 1  │───────┘                            │
│  │  (I₂)    │       │  (H₁)    │                                    │
│  └──────────┘       └──────────┘       ┌──────────┐                 │
│                                         │  Output  │                 │
│                                         │  Node 2  │                 │
│                                         │  (O₂)    │                 │
│                                         └──────────┘                 │
│                                                                      │
│  Only edges with W̃ = 1 remain active                                │
│  Network topology learned through training, not predefined          │
└─────────────────────────────────────────────────────────────────────┘
```

## Key Components

### 1. Graph Representation
- **Nodes**: Input (I), Hidden (H), Output (O)
- **Edges**: Directed connections with learnable weights
- **Adjacency Matrix**: W ∈ ℝ^(N×N) where N = total nodes

### 2. Weight Semantics
- **Continuous Phase**: W ∈ ℝ (can be any real number)
- **Discrete Phase**: W̃ ∈ {0, 1} (binary structure)
- **Mapping**: Inactive (W̃=0) vs Active (W̃=1)

### 3. Training Mechanism
- **Gradient-Based**: Standard backpropagation for continuous optimization
- **Structure Learning**: Discrete rounding to discover sparse topology
- **Interleaving**: Alternate between continuous and discrete phases

## Information Flow

```
Input Data (X)
     │
     ▼
[Dense Graph with W ∈ ℝ]
     │
     ├──▶ Forward Pass ──▶ Predictions (ŷ)
     │                          │
     │                          ▼
     │                     Loss L(ŷ, y)
     │                          │
     │                          ▼
     ◀── Backward Pass ◀── Gradients ∂L/∂W
     │
     ▼
[Update W with gradient descent]
     │
     ▼
[Round W → W̃ ∈ {0, 1}]
     │
     ▼
[Sparse Structure Emerges]
     │
     ▼
  Repeat until convergence
```

## Design Principles

1. **No Predefined Architecture**: Start with fully connected graph
2. **Structure via Pruning**: Weights → 0 eliminate connections
3. **Differentiable Core**: Use standard gradient descent
4. **Discrete Projection**: Periodic rounding enforces binary structure
5. **End-to-End Learning**: Both structure and parameters learned jointly
