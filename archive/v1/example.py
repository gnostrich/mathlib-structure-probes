"""
Example: Structure-First Backpropagation Demo

This script demonstrates the Structure-First Backpropagation algorithm
on a simple task (XOR problem) to show how structure emerges during training.
"""

import torch
import numpy as np
import matplotlib.pyplot as plt
from structure_backprop import StructureBackpropNetwork, train_structure_backprop
from visualization import (
    visualize_structure, 
    plot_training_history, 
    visualize_embeddings,
    create_summary_report,
    ensure_output_dir
)
from utils import set_seed, train_val_test_split
from export_utils import ensure_output_dir as export_dir, save_training_plot, save_metrics


def create_xor_dataset(n_samples: int = 100) -> tuple:
    """
    Create XOR dataset for testing structure learning.
    
    XOR is a classic non-linearly separable problem that requires
    at least one hidden layer to solve.
    
    Args:
        n_samples: Number of samples per class
        
    Returns:
        (X, y) tensors
    """
    # Create XOR data: [0,0]->0, [0,1]->1, [1,0]->1, [1,1]->0
    X = []
    y = []
    
    for _ in range(n_samples // 4):
        X.extend([[0, 0], [0, 1], [1, 0], [1, 1]])
        y.extend([[0], [1], [1], [0]])
    
    # Add some noise
    X = np.array(X, dtype=np.float32)
    X += np.random.randn(*X.shape) * 0.1
    y = np.array(y, dtype=np.float32)
    
    return torch.tensor(X), torch.tensor(y)


def create_addition_dataset(n_samples: int = 200) -> tuple:
    """
    Create a simple addition dataset: output = input1 + input2
    
    This is a linear problem that shouldn't require hidden nodes,
    so we expect the structure to learn direct input->output connections.
    
    Args:
        n_samples: Number of samples
        
    Returns:
        (X, y) tensors
    """
    X = torch.randn(n_samples, 2)
    y = X.sum(dim=1, keepdim=True)
    return X, y


def visualize_structure(model: StructureBackpropNetwork, title: str = "Learned Structure", task_name: str = None):
    """
    Visualize the learned graph structure.
    
    Note: This is kept for backward compatibility. 
    New code should use visualization.visualize_structure() directly.
    
    Args:
        model: Trained StructureBackpropNetwork
        title: Plot title
        task_name: Optional task name for saving outputs
    """
    from visualization import visualize_structure as viz_struct
    return viz_struct(model, title=title, task_name=task_name, interactive=False)


def plot_training_history(history: dict, title: str = "Training History", task_name: str = None):
    """
    Plot training metrics over time.
    
    Note: This is kept for backward compatibility.
    New code should use visualization.plot_training_history() directly.
    
    Args:
        history: Dictionary with 'loss', 'sparsity', 'active_edges'
        title: Plot title
        task_name: Optional task name for saving outputs
    """
    from visualization import plot_training_history as plot_hist
    return plot_hist(history, title=title, task_name=task_name, interactive=False)


def print_structure_summary(model: StructureBackpropNetwork):
    """Print a summary of the learned structure."""
    print("\n" + "="*60)
    print("LEARNED STRUCTURE SUMMARY")
    print("="*60)
    
    edges = model.get_structure()
    
    # Categorize edges
    input_to_hidden = []
    input_to_output = []
    hidden_to_hidden = []
    hidden_to_output = []
    
    for src, tgt in edges:
        src_type = 'input' if src < model.n_input else ('hidden' if src < model.n_input + model.n_hidden else 'output')
        tgt_type = 'input' if tgt < model.n_input else ('hidden' if tgt < model.n_input + model.n_hidden else 'output')
        
        if src_type == 'input' and tgt_type == 'hidden':
            input_to_hidden.append((src, tgt - model.n_input))
        elif src_type == 'input' and tgt_type == 'output':
            input_to_output.append((src, tgt - model.n_input - model.n_hidden))
        elif src_type == 'hidden' and tgt_type == 'hidden':
            hidden_to_hidden.append((src - model.n_input, tgt - model.n_input))
        elif src_type == 'hidden' and tgt_type == 'output':
            hidden_to_output.append((src - model.n_input, tgt - model.n_input - model.n_hidden))
    
    print(f"Total active edges: {len(edges)}")
    print(f"Sparsity: {model.get_sparsity():.2%}")
    print()
    
    print(f"Input → Hidden: {len(input_to_hidden)} edges")
    for src, tgt in input_to_hidden[:5]:  # Show first 5
        print(f"  Input_{src} → Hidden_{tgt}")
    if len(input_to_hidden) > 5:
        print(f"  ... and {len(input_to_hidden) - 5} more")
    print()
    
    print(f"Input → Output: {len(input_to_output)} edges")
    for src, tgt in input_to_output:
        print(f"  Input_{src} → Output_{tgt}")
    print()
    
    print(f"Hidden → Hidden: {len(hidden_to_hidden)} edges")
    for src, tgt in hidden_to_hidden[:5]:
        print(f"  Hidden_{src} → Hidden_{tgt}")
    if len(hidden_to_hidden) > 5:
        print(f"  ... and {len(hidden_to_hidden) - 5} more")
    print()
    
    print(f"Hidden → Output: {len(hidden_to_output)} edges")
    for src, tgt in hidden_to_output:
        print(f"  Hidden_{src} → Output_{tgt}")
    
    print("="*60 + "\n")


def demo_xor():
    """Demonstrate structure learning on XOR problem."""
    print("\n" + "="*60)
    print("DEMO 1: XOR PROBLEM")
    print("="*60)
    print("XOR is non-linearly separable and requires hidden nodes.")
    print("Expected: Network should learn to use hidden nodes.\n")
    
    # Create dataset
    X, y = create_xor_dataset(n_samples=200)
    print(f"Dataset: {X.shape[0]} samples, {X.shape[1]} features")
    
    # Create model
    model = StructureBackpropNetwork(
        n_input=2,
        n_hidden=4,
        n_output=1,
        rounding_threshold=0.3,
        activation='relu'
    )
    
    print(f"Model: {model.n_input} input, {model.n_hidden} hidden, {model.n_output} output nodes")
    print(f"Initial active edges: {model.get_active_edges()}")
    
    # Train
    history = train_structure_backprop(
        model=model,
        train_data=(X, y),
        n_epochs=500,
        learning_rate=0.01,
        rounding_frequency=50,
        rounding_method='threshold',
        verbose=True
    )
    
    # Evaluate
    with torch.no_grad():
        predictions = model(X)
        final_loss = torch.nn.functional.mse_loss(predictions, y)
        accuracy = ((predictions > 0.5) == (y > 0.5)).float().mean()
    
    print(f"\nFinal Loss: {final_loss.item():.4f}")
    print(f"Accuracy: {accuracy.item():.2%}")
    
    # Show structure
    print_structure_summary(model)
    
    # Visualize
    try:
        # Save static visualizations
        fig1 = visualize_structure(model, "XOR Problem - Learned Structure", task_name='xor')
        fig2 = plot_training_history(history, "XOR Problem - Training History", task_name='xor')
        
        # Create embedding visualization
        visualize_embeddings(model, X, y, method='umap', 
                           title='XOR - Hidden Layer Embeddings (UMAP)',
                           task_name='xor')
        
        # Create summary report
        final_metrics = {
            'final_loss': final_loss.item(),
            'accuracy': accuracy.item()
        }
        create_summary_report(model, history, final_metrics, 'xor')
        
        plt.close('all')
    except Exception as e:
        print(f"Visualization error: {e}")
    
    # Export static outputs for Phase 3
    try:
        output_dir = export_dir('xor')
        save_training_plot(history, 'xor', output_dir)
        save_metrics(final_metrics, 'xor', output_dir)
        print(f"✓ Outputs saved to {output_dir}")
    except Exception as e:
        print(f"Export error: {e}")
    
    return model, history


def demo_addition():
    """Demonstrate structure learning on simple addition problem."""
    print("\n" + "="*60)
    print("DEMO 2: ADDITION PROBLEM (LINEAR)")
    print("="*60)
    print("Task: output = input1 + input2 (linear, no hidden nodes needed)")
    print("Expected: Network should learn direct input→output connections.\n")
    
    # Create dataset
    X, y = create_addition_dataset(n_samples=200)
    print(f"Dataset: {X.shape[0]} samples, {X.shape[1]} features")
    
    # Create model
    model = StructureBackpropNetwork(
        n_input=2,
        n_hidden=3,
        n_output=1,
        rounding_threshold=0.3,
        activation='relu'
    )
    
    print(f"Model: {model.n_input} input, {model.n_hidden} hidden, {model.n_output} output nodes")
    print(f"Initial active edges: {model.get_active_edges()}")
    
    # Train
    history = train_structure_backprop(
        model=model,
        train_data=(X, y),
        n_epochs=300,
        learning_rate=0.01,
        rounding_frequency=30,
        rounding_method='threshold',
        verbose=True
    )
    
    # Evaluate
    with torch.no_grad():
        predictions = model(X)
        mse_loss = torch.nn.functional.mse_loss(predictions, y)
        mae_loss = torch.nn.functional.l1_loss(predictions, y)
        # Compute R² score
        ss_res = ((predictions - y) ** 2).sum()
        ss_tot = ((y - y.mean()) ** 2).sum()
        r_squared = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0
    
    print(f"\nFinal Loss (MSE): {mse_loss.item():.6f}")
    print(f"Mean Absolute Error (MAE): {mae_loss.item():.6f}")
    print(f"R² Score: {r_squared:.4f}")
    
    # Show structure
    print_structure_summary(model)
    
    # Visualize
    try:
        # Save static visualizations
        fig1 = visualize_structure(model, "Addition Problem - Learned Structure", task_name='addition')
        fig2 = plot_training_history(history, "Addition Problem - Training History", task_name='addition')
        
        # Create embedding visualization
        visualize_embeddings(model, X, y, method='umap',
                           title='Addition - Hidden Layer Embeddings (UMAP)',
                           task_name='addition')
        
        # Create summary report
        final_metrics = {
            'mse_loss': mse_loss.item(),
            'mae_loss': mae_loss.item(),
            'r_squared': r_squared
        }
        create_summary_report(model, history, final_metrics, 'addition')
        
        plt.close('all')
    except Exception as e:
        print(f"Visualization error: {e}")
    
    # Export static outputs for Phase 3
    try:
        output_dir = export_dir('addition')
        save_training_plot(history, 'addition', output_dir)
        save_metrics(final_metrics, 'addition', output_dir)
        print(f"✓ Outputs saved to {output_dir}")
    except Exception as e:
        print(f"Export error: {e}")
    
    return model, history


if __name__ == "__main__":
    print("\n" + "="*60)
    print("STRUCTURE-FIRST BACKPROPAGATION - DEMONSTRATIONS")
    print("="*60)
    
    # Set random seed for reproducibility
    torch.manual_seed(42)
    np.random.seed(42)
    
    # Run demonstrations
    xor_model, xor_history = demo_xor()
    addition_model, addition_history = demo_addition()
    
    print("\n" + "="*60)
    print("ALL DEMONSTRATIONS COMPLETED")
    print("="*60)
    print("\nKey Observations:")
    print("1. XOR (non-linear) requires hidden nodes - structure should reflect this")
    print("2. Addition (linear) may learn direct input→output paths")
    print("3. Structure sparsity increases during training as weak connections are pruned")
    print("4. The algorithm discovers problem-appropriate architectures automatically")
    
    # Create outputs README
    try:
        from export_utils import create_outputs_readme
        create_outputs_readme(['xor', 'addition'])
        print("\n✓ Outputs folder created with README")
    except Exception as e:
        print(f"\nWarning: Could not create outputs README: {e}")
