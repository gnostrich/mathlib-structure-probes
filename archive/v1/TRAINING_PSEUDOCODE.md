# Training Loop Pseudocode

## Algorithm: Structure-First Backpropagation

```
ALGORITHM: StructureFirstBackprop
──────────────────────────────────────────────────────────────────

INPUT:
  - X: Training data (input features)
  - Y: Training labels (targets)
  - n_input: Number of input nodes
  - n_hidden: Number of hidden nodes  
  - n_output: Number of output nodes
  - n_epochs: Number of training epochs
  - rounding_frequency: How often to round weights (e.g., every k steps)
  - learning_rate: Step size for gradient descent
  - rounding_threshold: Threshold for binary rounding

OUTPUT:
  - W: Learned weight matrix (sparse, binary structure)
  - Structure: Discovered graph topology

──────────────────────────────────────────────────────────────────

INITIALIZATION:
  1. n_total ← n_input + n_hidden + n_output
  2. W ← random_uniform(n_total, n_total)  // Dense adjacency matrix
  3. Mark input_nodes, hidden_nodes, output_nodes
  4. Enforce directed graph constraints (no backward edges if desired)

TRAINING LOOP:
  FOR epoch = 1 TO n_epochs DO:
    
    FOR each batch (X_batch, Y_batch) in training_data DO:
      
      ─────────────────────────────────────────────────────────
      PHASE 1: CONTINUOUS OPTIMIZATION (Standard Backprop)
      ─────────────────────────────────────────────────────────
      
      // Forward Pass
      activations ← FORWARD_PASS(X_batch, W)
      predictions ← activations[output_nodes]
      
      // Compute Loss
      loss ← LOSS_FUNCTION(predictions, Y_batch)
      
      // Backward Pass
      gradients ← BACKWARD_PASS(loss, W, activations)
      
      // Update Weights (continuous domain)
      W ← W - learning_rate * gradients
      
      ─────────────────────────────────────────────────────────
      PHASE 2: DISCRETE STRUCTURE PROJECTION
      ─────────────────────────────────────────────────────────
      
      IF step_count % rounding_frequency == 0 THEN:
        // Round weights to binary values
        W ← ROUND_WEIGHTS(W, rounding_threshold)
        
        // Optional: Analyze structure sparsity
        active_edges ← COUNT_NONZERO(W)
        PRINT("Active edges: ", active_edges)
      
      step_count ← step_count + 1
    
    END FOR
    
    // Epoch-level evaluation
    val_loss ← EVALUATE(validation_data, W)
    PRINT("Epoch ", epoch, " - Loss: ", loss, " - Val Loss: ", val_loss)
  
  END FOR

RETURN W, EXTRACT_STRUCTURE(W)

──────────────────────────────────────────────────────────────────

SUBROUTINE: FORWARD_PASS(X, W)
──────────────────────────────────────────────────────────────────
INPUT: X (batch of inputs), W (weight matrix)
OUTPUT: activations (all node activations)

  1. activations ← zeros(n_total, batch_size)
  2. activations[input_nodes] ← X
  
  3. FOR each layer in topological_order DO:
       FOR each node i in current_layer DO:
         // Aggregate incoming signals
         incoming ← SUM over j: W[j, i] * activations[j]
         
         // Apply activation function
         activations[i] ← ACTIVATION_FUNCTION(incoming)
       END FOR
  END FOR
  
  RETURN activations

──────────────────────────────────────────────────────────────────

SUBROUTINE: BACKWARD_PASS(loss, W, activations)
──────────────────────────────────────────────────────────────────
INPUT: loss (scalar), W (weights), activations (from forward pass)
OUTPUT: gradients (∂loss/∂W)

  1. gradients ← zeros_like(W)
  2. output_gradients ← ∂loss/∂activations[output_nodes]
  
  3. FOR each layer in reverse_topological_order DO:
       // Backpropagate through activation functions
       node_gradients ← output_gradients * ACTIVATION_DERIVATIVE(activations)
       
       // Compute weight gradients
       FOR each edge (j, i) with weight W[j, i] DO:
         gradients[j, i] ← node_gradients[i] * activations[j]
       END FOR
       
       // Propagate gradients to previous layer
       output_gradients ← W^T @ node_gradients
  END FOR
  
  RETURN gradients

──────────────────────────────────────────────────────────────────

SUBROUTINE: ROUND_WEIGHTS(W, threshold)
──────────────────────────────────────────────────────────────────
INPUT: W (continuous weight matrix), threshold
OUTPUT: W_rounded (binary weight matrix)

  METHOD 1 (Threshold-based):
    FOR each weight W[i, j] DO:
      IF |W[i, j]| < threshold THEN:
        W[i, j] ← 0
      ELSE:
        W[i, j] ← 1
      END IF
    END FOR
  
  METHOD 2 (Sigmoid-based):
    FOR each weight W[i, j] DO:
      IF sigmoid(W[i, j]) < 0.5 THEN:
        W[i, j] ← 0
      ELSE:
        W[i, j] ← 1
      END IF
    END FOR
  
  METHOD 3 (Direct rounding):
    FOR each weight W[i, j] DO:
      W[i, j] ← ROUND(W[i, j])  // Round to nearest integer
      W[i, j] ← CLIP(W[i, j], 0, 1)  // Ensure in {0, 1}
    END FOR
  
  RETURN W

──────────────────────────────────────────────────────────────────

SUBROUTINE: EXTRACT_STRUCTURE(W)
──────────────────────────────────────────────────────────────────
INPUT: W (binary weight matrix)
OUTPUT: graph_structure (adjacency list or edge list)

  graph ← empty_graph()
  
  FOR i = 1 TO n_total DO:
    FOR j = 1 TO n_total DO:
      IF W[i, j] == 1 THEN:
        graph.add_edge(i, j)
      END IF
    END FOR
  END FOR
  
  RETURN graph

──────────────────────────────────────────────────────────────────
```

## Variants and Extensions

### Variant 1: Soft Rounding (Gumbel-Softmax)
Instead of hard rounding, use a soft approximation that remains differentiable:
```
W_soft = sigmoid((W - 0.5) / temperature)
```
As training progresses, decrease temperature to approach binary values.

### Variant 2: Stochastic Rounding
```
FOR each weight W[i, j] DO:
  p = sigmoid(W[i, j])
  W[i, j] = BERNOULLI_SAMPLE(p)  // Sample from Bernoulli distribution
END FOR
```

### Variant 3: Top-K Sparsification
Instead of threshold-based rounding:
```
1. Sort all weights by magnitude
2. Keep top-k% of weights, set rest to 0
3. Set kept weights to 1
```

## Hyperparameter Guidelines

- **rounding_frequency**: Start with every 10-100 steps, adjust based on stability
- **rounding_threshold**: Try 0.3-0.5 for threshold-based rounding
- **learning_rate**: Use standard rates (0.001-0.01), may need lower rates near rounding steps
- **initialization**: Small random values (e.g., uniform(-0.1, 0.1))

## Monitoring Metrics

During training, track:
1. **Loss**: Task-specific objective (MSE, CrossEntropy, etc.)
2. **Sparsity**: Percentage of weights == 0
3. **Active Edges**: Count of non-zero weights
4. **Structure Stability**: How much structure changes between rounds
