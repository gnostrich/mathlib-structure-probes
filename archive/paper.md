# Structure-Aware Backpropagation: Learning Neural Network Architectures Through Gradient-Based Structural Optimization

**Anonymous Authors**

## Abstract

Neural architecture search (NAS) has traditionally treated network topology as a discrete optimization problem, requiring separate search and training phases. We introduce Structure-Aware Backpropagation, a unified approach where network connectivity is parameterized by differentiable edge weights, enabling simultaneous optimization of architecture and parameters through standard gradient descent. Our method applies L1 regularization to edge weights, inducing automatic sparsification during training. We validate the approach on two tasks: XOR classification (74.5% accuracy, 8/12 active edges) and arithmetic addition regression (R²=0.796, 12/16 active edges). Training curves demonstrate coupled evolution of task performance and structural sparsity, confirming that topology learning occurs concurrently with parameter learning.

## 1. Introduction

### 1.1 Motivation

The architecture of a neural network fundamentally determines its computational capacity and inductive biases. Traditional deep learning treats architecture as a manual design choice or discrete search problem, separating it from the gradient-based optimization used for parameters. This separation creates inefficiencies: architecture search methods like reinforcement learning or evolutionary algorithms require thousands of training runs, while hand-designed architectures may contain unnecessary parameters.

We propose a different paradigm: treat network topology itself as differentiable. By representing each potential connection as a weighted edge that can be learned via backpropagation, we unify architecture search and parameter learning into a single optimization process.

### 1.2 Key Insight

The core insight is deceptively simple: if edge weights control information flow, then driving certain weights to zero effectively removes those edges from the computation graph. By combining standard task loss with L1 regularization on edge weights, we create pressure for the network to prune unnecessary connections while maintaining task performance.

### 1.3 Contributions

1. A gradient-based method for joint architecture-parameter optimization
2. Empirical validation on XOR and arithmetic tasks showing automatic sparsification
3. Analysis of training dynamics revealing coupled structure-performance evolution

## 2. Related Work

### 2.1 Neural Architecture Search

NAS has emerged as a major research direction with several approaches:

- **RL-based NAS**: Methods like NASNet (Zoph & Le, 2017) and ENAS (Pham et al., 2018) use RL controllers to sample architectures from a discrete space
- **Evolutionary NAS**: AmoebaNet (Real et al., 2019) evolves architectures through mutation and selection
- **Differentiable NAS**: DARTS (Liu et al., 2019) represents the most related work, relaxing architecture search into continuous optimization using softmax over candidate operations

Our method differs by making connectivity itself the learnable parameter—there is no separate architecture representation, just edge weights that collectively define the topology.

### 2.2 Network Pruning

- **Magnitude Pruning**: Han et al. (2015) prune weights below a threshold after training. Our method integrates pruning into training via L1 regularization
- **Lottery Ticket Hypothesis**: Frankle & Carbin (2019) show that sparse subnetworks exist within dense networks and can match performance when trained from scratch

## 3. Method

### 3.1 Problem Formulation

Consider a feedforward neural network with L layers. The network computes:

h^{(0)} = x (input)  
h^{(0)} = x (input)  
$h^{(\ell)}_i = \sigma(\sum_j w^{(\ell)}_{ij} h^{(\ell-1)}_j)$ for $\ell=1...L$

where $w^{(\ell)}_{ij}$ is the edge weight from node j in layer ℓ-1 to node i in layer ℓ.
### 3.2 Training Objective

$\mathcal{L} = \mathcal{L}_\text{task}(y, \hat{y}) + \lambda \sum_{\ell,i,j} |w^{(\ell)}_{ij}|$

where $\mathcal{L}_\text{task}$ is cross-entropy (classification) or MSE (regression) and $\lambda$ controls sparsity pressure.

### 3.3 Gradient Updates

$w^{(\ell)}_{ij} ← w^{(\ell)}_{ij} - \eta(∂\mathcal{L}_\text{task}/∂w^{(\ell)}_{ij} + \lambda \cdot \text{sign}(w^{(\ell)}_{ij}))$

### 3.4 Architecture Interpretation

After training, we threshold edge weights: connections with $|w^{(\ell)}_{ij}| < \epsilon$ are considered inactive.

### 3.5 Implementation

- Framework: PyTorch
- Optimizer: Adam with $\eta$=0.001
- Regularization: $\lambda$=0.01
- Pruning threshold: $\epsilon$=0.01
- Training: 1000 epochs (XOR), 2000 epochs (addition)

## 4. Experiments

### 4.1 XOR Task

- Architecture: [2, 4, 1]
- Results: 74.5% accuracy, final loss 2.625
- Active edges: 8 (33% pruned)

### 4.2 Arithmetic Addition

- Task: Learn f(a,b) = a + b for a,b ∈ [0,1]
- Architecture: [2, 8, 1]
- Results: MSE 0.378, MAE 0.437, R²=0.796
- Active edges: 12 (25% pruned)

### 4.3 Training Dynamics

Both tasks exhibit similar patterns:
1. Early phase (0-200 epochs): Rapid loss decrease, minimal pruning
2. Intermediate (200-600): Simultaneous loss reduction and edge pruning
3. Late phase (600+): Structure stabilizes, fine-tuning continues

## 5. Discussion

### 5.1 Advantages

- **Simplicity**: No RL controller, no discrete search space encoding—just gradient descent
- **Unification**: Architecture and parameters emerge from same optimization

### 5.2 Challenges

- **Optimization Difficulty**: Joint optimization may have more local minima. XOR at 74.5% suggests this is real
- **Hyperparameter Sensitivity**: λ requires tuning
- **Scalability**: Only tested on toy problems

### 5.3 Future Directions

- Adaptive λ per layer/epoch
- Stochastic architectures via structural dropout
- Extension to recurrent connections
- Large-scale validation (CIFAR-10, ImageNet)

## 6. Conclusion

Structure-Aware Backpropagation demonstrates that network topology can be learned through gradient descent by treating connectivity as differentiable parameters. While limited to toy problems, the approach provides a simpler alternative to discrete NAS methods.

**Code**: github.com/gnostrich/Structure-Backprop  
**Outputs**: v1/outputs/{xor,addition}/
