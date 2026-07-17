"""
Structure-First Backpropagation - PyTorch Implementation

This module implements the Structure-First Backpropagation algorithm
where a dense directed graph learns its structure through training by
alternating between continuous gradient descent and discrete weight rounding.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
from typing import Tuple, Optional, List


class StructureBackpropNetwork(nn.Module):
    """
    A neural network that learns its structure through training.
    
    The network starts as a fully connected directed graph and learns
    which connections to keep (weight=1) or remove (weight=0) through
    alternating gradient descent and weight rounding steps.
    """
    
    def __init__(
        self,
        n_input: int,
        n_hidden: int,
        n_output: int,
        rounding_threshold: float = 0.5,
        activation: str = 'relu'
    ):
        """
        Initialize a dense directed graph.
        
        Args:
            n_input: Number of input nodes
            n_hidden: Number of hidden nodes
            n_output: Number of output nodes
            rounding_threshold: Threshold for binary rounding (0-1)
            activation: Activation function ('relu', 'tanh', 'sigmoid')
        """
        super().__init__()
        
        self.n_input = n_input
        self.n_hidden = n_hidden
        self.n_output = n_output
        self.n_total = n_input + n_hidden + n_output
        self.rounding_threshold = rounding_threshold
        
        # Define node ranges
        self.input_range = (0, n_input)
        self.hidden_range = (n_input, n_input + n_hidden)
        self.output_range = (n_input + n_hidden, self.n_total)
        
        # Initialize dense adjacency matrix as parameter
        # Use small random initialization
        self.weights = nn.Parameter(
            torch.randn(self.n_total, self.n_total) * 0.1
        )
        
        # Mask for enforcing directed graph structure (optional)
        # This prevents connections that would create invalid flows
        self.register_buffer('structure_mask', self._create_structure_mask())
        
        # Set activation function
        if activation == 'relu':
            self.activation = F.relu
        elif activation == 'tanh':
            self.activation = torch.tanh
        elif activation == 'sigmoid':
            self.activation = torch.sigmoid
        else:
            raise ValueError(f"Unknown activation: {activation}")
    
    def _create_structure_mask(self) -> torch.Tensor:
        """
        Create a mask to enforce directed graph structure.
        
        Allows connections:
        - Input -> Hidden
        - Input -> Output  
        - Hidden -> Hidden
        - Hidden -> Output
        
        Prevents:
        - Output -> anything
        - Hidden -> Input
        - Output -> Input
        """
        mask = torch.zeros(self.n_total, self.n_total)
        
        # Input nodes can connect to hidden and output
        mask[self.input_range[0]:self.input_range[1], 
             self.hidden_range[0]:self.output_range[1]] = 1
        
        # Hidden nodes can connect to hidden and output
        mask[self.hidden_range[0]:self.hidden_range[1],
             self.hidden_range[0]:self.output_range[1]] = 1
        
        # Output nodes don't connect to anything (terminal nodes)
        
        return mask
    
    def forward(self, x: torch.Tensor, use_rounded: bool = False) -> torch.Tensor:
        """
        Forward pass through the graph.
        
        Args:
            x: Input tensor of shape (batch_size, n_input)
            use_rounded: If True, use rounded binary weights
            
        Returns:
            Output tensor of shape (batch_size, n_output)
        """
        batch_size = x.shape[0]
        
        # Initialize activations for all nodes
        activations = torch.zeros(batch_size, self.n_total, device=x.device)
        
        # Set input node activations (create new tensor to avoid in-place)
        activations = torch.cat([
            x,
            torch.zeros(batch_size, self.n_hidden + self.n_output, device=x.device)
        ], dim=1)
        
        # Get effective weights (masked and optionally rounded)
        if use_rounded:
            effective_weights = self.get_rounded_weights()
        else:
            effective_weights = self.weights * self.structure_mask
        
        # Process hidden nodes (accumulate inputs from previous layers)
        hidden_activations = []
        for i in range(self.hidden_range[0], self.hidden_range[1]):
            # Sum weighted inputs from all previous nodes
            incoming = torch.matmul(activations, effective_weights[:, i])
            hidden_activations.append(self.activation(incoming).unsqueeze(1))
        
        # Update hidden activations
        if hidden_activations:
            activations = torch.cat([
                activations[:, :self.hidden_range[0]],
                torch.cat(hidden_activations, dim=1),
                activations[:, self.output_range[0]:]
            ], dim=1)
        
        # Process output nodes
        output_activations = []
        for i in range(self.output_range[0], self.output_range[1]):
            # Sum weighted inputs from all previous nodes
            incoming = torch.matmul(activations, effective_weights[:, i])
            output_activations.append(incoming.unsqueeze(1))
        
        # Extract output activations
        output = torch.cat(output_activations, dim=1) if output_activations else torch.zeros(batch_size, self.n_output, device=x.device)
        
        return output
    
    def round_weights(self, method: str = 'threshold') -> None:
        """
        Round weights to binary values {0, 1}.
        
        Args:
            method: Rounding method ('threshold', 'sigmoid', 'hard')
        """
        with torch.no_grad():
            if method == 'threshold':
                # Threshold-based: weights below threshold become 0
                mask = torch.abs(self.weights) >= self.rounding_threshold
                self.weights.data = mask.float()
            
            elif method == 'sigmoid':
                # Sigmoid-based: use sigmoid and threshold at 0.5
                probs = torch.sigmoid(self.weights)
                self.weights.data = (probs >= 0.5).float()
            
            elif method == 'hard':
                # Hard rounding: round to nearest integer and clip to [0, 1]
                self.weights.data = torch.clamp(torch.round(self.weights), 0, 1)
            
            else:
                raise ValueError(f"Unknown rounding method: {method}")
            
            # Re-apply structure mask after rounding
            self.weights.data *= self.structure_mask
    
    def get_rounded_weights(self) -> torch.Tensor:
        """Get current weights rounded to binary without modifying them."""
        with torch.no_grad():
            probs = torch.sigmoid(self.weights)
            rounded = (probs >= 0.5).float()
            return rounded * self.structure_mask
    
    def get_sparsity(self) -> float:
        """Calculate the current sparsity (percentage of zero weights)."""
        with torch.no_grad():
            # Only consider weights that could be active (within structure mask)
            possible_weights = self.structure_mask.sum()
            # Count zeros only where mask is 1 (valid positions)
            active_weights = self.weights * self.structure_mask
            zero_weights = ((active_weights == 0) & (self.structure_mask == 1)).sum()
            return (zero_weights / possible_weights).item()
    
    def get_active_edges(self) -> int:
        """Count the number of active (non-zero) edges."""
        with torch.no_grad():
            return ((self.weights * self.structure_mask) != 0).sum().item()
    
    def get_structure(self) -> List[Tuple[int, int]]:
        """
        Extract the learned structure as a list of edges.
        
        Returns:
            List of (source, target) tuples for non-zero weights
        """
        with torch.no_grad():
            active_weights = self.weights * self.structure_mask
            edges = []
            for i in range(self.n_total):
                for j in range(self.n_total):
                    if active_weights[i, j] != 0:
                        edges.append((i, j))
            return edges


def train_structure_backprop(
    model: StructureBackpropNetwork,
    train_data: Tuple[torch.Tensor, torch.Tensor],
    n_epochs: int,
    learning_rate: float = 0.01,
    rounding_frequency: int = 10,
    rounding_method: str = 'threshold',
    verbose: bool = True
) -> dict:
    """
    Train a Structure-First Backpropagation model.
    
    Args:
        model: StructureBackpropNetwork instance
        train_data: Tuple of (X_train, y_train) tensors
        n_epochs: Number of training epochs
        learning_rate: Learning rate for optimizer
        rounding_frequency: Round weights every N steps
        rounding_method: Method for rounding ('threshold', 'sigmoid', 'hard')
        verbose: Print training progress
        
    Returns:
        Dictionary with training history
    """
    X_train, y_train = train_data
    
    # Determine task type and loss function
    if y_train.dim() == 1 or y_train.shape[1] == 1:
        # Regression or binary classification
        criterion = nn.MSELoss()
    else:
        # Multi-class classification
        criterion = nn.CrossEntropyLoss()
    
    optimizer = torch.optim.Adam(model.parameters(), lr=learning_rate)
    
    history = {
        'loss': [],
        'sparsity': [],
        'active_edges': []
    }
    
    step_count = 0
    
    for epoch in range(n_epochs):
        # Forward pass
        predictions = model(X_train)
        
        # Compute loss
        if predictions.shape != y_train.shape and y_train.dim() > 1:
            # For multi-class, y might need to be indices
            loss = criterion(predictions, y_train.argmax(dim=1))
        else:
            loss = criterion(predictions, y_train)
        
        # Backward pass
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
        
        # Periodic weight rounding
        if step_count % rounding_frequency == 0 and step_count > 0:
            model.round_weights(method=rounding_method)
        
        step_count += 1
        
        # Record metrics
        history['loss'].append(loss.item())
        history['sparsity'].append(model.get_sparsity())
        history['active_edges'].append(model.get_active_edges())
        
        # Print progress
        if verbose and (epoch % max(1, n_epochs // 10) == 0 or epoch == n_epochs - 1):
            print(f"Epoch {epoch:4d} | Loss: {loss.item():.4f} | "
                  f"Sparsity: {model.get_sparsity():.2%} | "
                  f"Active Edges: {model.get_active_edges()}")
    
    return history


if __name__ == "__main__":
    # This will be demonstrated in the example script
    print("Structure-First Backpropagation module loaded successfully.")
    print("See example.py for usage demonstrations.")
