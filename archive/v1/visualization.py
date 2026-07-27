"""
Enhanced Visualization Module for Structure-First Backpropagation

This module provides advanced visualization capabilities including:
- Interactive dashboards (Streamlit/Plotly)
- Clustering visualizations (UMAP/t-SNE)
- Automated output management
- Real-time training visualization
"""

import os
import torch
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from typing import Optional, Dict, List, Tuple
from datetime import datetime


def ensure_output_dir(task_name: str) -> Path:
    """
    Ensure output directory exists for a specific task.
    
    Args:
        task_name: Name of the task (e.g., 'xor', 'addition')
        
    Returns:
        Path to the output directory
    """
    output_dir = Path(__file__).parent / 'outputs' / 'v1' / task_name
    output_dir.mkdir(parents=True, exist_ok=True)
    return output_dir


def save_plot(fig, filename: str, task_name: str, dpi: int = 150):
    """
    Save a plot to the appropriate output directory.
    
    Args:
        fig: Matplotlib figure
        filename: Name of the file (without path)
        task_name: Name of the task (e.g., 'xor', 'addition')
        dpi: Resolution of saved image
    """
    output_dir = ensure_output_dir(task_name)
    filepath = output_dir / filename
    fig.savefig(filepath, dpi=dpi, bbox_inches='tight')
    print(f"Saved: {filepath}")


def visualize_structure(
    model,
    title: str = "Learned Structure",
    save_path: Optional[str] = None,
    task_name: Optional[str] = None,
    interactive: bool = False
):
    """
    Visualize the learned graph structure with optional interactivity.
    
    Args:
        model: Trained StructureBackpropNetwork
        title: Plot title
        save_path: Optional path to save the plot
        task_name: Task name for automatic output management
        interactive: If True, use Plotly for interactive visualization
        
    Returns:
        Figure object (matplotlib or plotly)
    """
    with torch.no_grad():
        weights = (model.weights * model.structure_mask).cpu().numpy()
    
    if interactive:
        try:
            import plotly.graph_objects as go
            
            # Create interactive heatmap
            fig = go.Figure(data=go.Heatmap(
                z=weights,
                colorscale='RdBu',
                zmid=0,
                zmin=-1,
                zmax=1,
                colorbar=dict(title='Weight Value'),
                hovertemplate='Source: %{y}<br>Target: %{x}<br>Weight: %{z:.3f}<extra></extra>'
            ))
            
            # Add labels
            y_labels = ['Input'] * model.n_input + ['Hidden'] * model.n_hidden + ['Output'] * model.n_output
            x_labels = y_labels
            
            fig.update_layout(
                title=title,
                xaxis=dict(
                    title='Target Node',
                    tickmode='array',
                    tickvals=list(range(model.n_total)),
                    ticktext=[f"{x_labels[i]}_{i}" for i in range(model.n_total)]
                ),
                yaxis=dict(
                    title='Source Node',
                    tickmode='array',
                    tickvals=list(range(model.n_total)),
                    ticktext=[f"{y_labels[i]}_{i}" for i in range(model.n_total)]
                ),
                width=800,
                height=700
            )
            
            if save_path:
                fig.write_html(save_path)
                print(f"Interactive visualization saved to: {save_path}")
            elif task_name:
                output_dir = ensure_output_dir(task_name)
                filepath = output_dir / f"{task_name}_structure_interactive.html"
                fig.write_html(str(filepath))
                print(f"Interactive visualization saved to: {filepath}")
            
            return fig
            
        except ImportError:
            print("Plotly not available. Falling back to matplotlib.")
            interactive = False
    
    # Standard matplotlib visualization
    fig = plt.figure(figsize=(10, 8))
    plt.imshow(weights, cmap='RdBu', vmin=-1, vmax=1, aspect='auto')
    plt.colorbar(label='Weight Value')
    
    # Add grid lines to separate node types
    plt.axhline(y=model.input_range[1] - 0.5, color='black', linewidth=2)
    plt.axhline(y=model.hidden_range[1] - 0.5, color='black', linewidth=2)
    plt.axvline(x=model.input_range[1] - 0.5, color='black', linewidth=2)
    plt.axvline(x=model.hidden_range[1] - 0.5, color='black', linewidth=2)
    
    # Add labels
    plt.ylabel('Source Node')
    plt.xlabel('Target Node')
    plt.title(title)
    
    # Add text annotations for node types
    y_labels = ['Input'] * model.n_input + ['Hidden'] * model.n_hidden + ['Output'] * model.n_output
    x_labels = y_labels
    
    plt.yticks(range(model.n_total), 
               [f"{y_labels[i]}_{i}" for i in range(model.n_total)],
               fontsize=8)
    plt.xticks(range(model.n_total),
               [f"{x_labels[i]}_{i}" for i in range(model.n_total)],
               rotation=90, fontsize=8)
    
    plt.tight_layout()
    
    if save_path:
        fig.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Structure visualization saved to: {save_path}")
    elif task_name:
        save_plot(fig, f"{task_name}_structure.png", task_name)
    
    return fig


def plot_training_history(
    history: Dict,
    title: str = "Training History",
    save_path: Optional[str] = None,
    task_name: Optional[str] = None,
    interactive: bool = False
):
    """
    Plot training metrics over time with optional interactivity.
    
    Args:
        history: Dictionary with 'loss', 'sparsity', 'active_edges'
        title: Plot title
        save_path: Optional path to save the plot
        task_name: Task name for automatic output management
        interactive: If True, use Plotly for interactive visualization
        
    Returns:
        Figure object
    """
    if interactive:
        try:
            import plotly.graph_objects as go
            from plotly.subplots import make_subplots
            
            # Create subplots
            fig = make_subplots(
                rows=1, cols=3,
                subplot_titles=('Training Loss', 'Network Sparsity', 'Active Edges')
            )
            
            epochs = list(range(len(history['loss'])))
            
            # Loss
            fig.add_trace(
                go.Scatter(x=epochs, y=history['loss'], mode='lines', name='Loss'),
                row=1, col=1
            )
            
            # Sparsity
            fig.add_trace(
                go.Scatter(x=epochs, y=history['sparsity'], mode='lines', name='Sparsity'),
                row=1, col=2
            )
            
            # Active edges
            fig.add_trace(
                go.Scatter(x=epochs, y=history['active_edges'], mode='lines', name='Active Edges'),
                row=1, col=3
            )
            
            fig.update_xaxes(title_text="Epoch", row=1, col=1)
            fig.update_xaxes(title_text="Epoch", row=1, col=2)
            fig.update_xaxes(title_text="Epoch", row=1, col=3)
            
            fig.update_yaxes(title_text="Loss", row=1, col=1)
            fig.update_yaxes(title_text="Sparsity (%)", row=1, col=2)
            fig.update_yaxes(title_text="Number of Edges", row=1, col=3)
            
            fig.update_layout(
                title_text=title,
                showlegend=False,
                width=1400,
                height=400
            )
            
            if save_path:
                fig.write_html(save_path)
                print(f"Interactive training history saved to: {save_path}")
            elif task_name:
                output_dir = ensure_output_dir(task_name)
                filepath = output_dir / f"{task_name}_history_interactive.html"
                fig.write_html(str(filepath))
                print(f"Interactive training history saved to: {filepath}")
            
            return fig
            
        except ImportError:
            print("Plotly not available. Falling back to matplotlib.")
            interactive = False
    
    # Standard matplotlib visualization
    fig, axes = plt.subplots(1, 3, figsize=(15, 4))
    
    # Loss
    axes[0].plot(history['loss'])
    axes[0].set_xlabel('Epoch')
    axes[0].set_ylabel('Loss')
    axes[0].set_title('Training Loss')
    axes[0].grid(True, alpha=0.3)
    
    # Sparsity
    axes[1].plot(history['sparsity'])
    axes[1].set_xlabel('Epoch')
    axes[1].set_ylabel('Sparsity (%)')
    axes[1].set_title('Network Sparsity')
    axes[1].grid(True, alpha=0.3)
    
    # Active edges
    axes[2].plot(history['active_edges'])
    axes[2].set_xlabel('Epoch')
    axes[2].set_ylabel('Number of Edges')
    axes[2].set_title('Active Edges')
    axes[2].grid(True, alpha=0.3)
    
    fig.suptitle(title, fontsize=14, fontweight='bold')
    plt.tight_layout()
    
    if save_path:
        fig.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Training history saved to: {save_path}")
    elif task_name:
        save_plot(fig, f"{task_name}_history.png", task_name)
    
    return fig


def visualize_embeddings(
    model,
    X: torch.Tensor,
    y: torch.Tensor,
    method: str = 'umap',
    title: Optional[str] = None,
    save_path: Optional[str] = None,
    task_name: Optional[str] = None
):
    """
    Visualize learned embeddings using dimensionality reduction.
    
    Args:
        model: Trained StructureBackpropNetwork
        X: Input data
        y: Labels for coloring
        method: Reduction method ('umap' or 'tsne')
        title: Plot title
        save_path: Optional path to save the plot
        task_name: Task name for automatic output management
        
    Returns:
        Matplotlib figure
    """
    # Get hidden layer activations
    with torch.no_grad():
        batch_size = X.shape[0]
        activations = torch.zeros(batch_size, model.n_total, device=X.device)
        
        # Set input activations
        activations = torch.cat([
            X,
            torch.zeros(batch_size, model.n_hidden + model.n_output, device=X.device)
        ], dim=1)
        
        # Get effective weights
        effective_weights = model.weights * model.structure_mask
        
        # Process hidden nodes
        hidden_activations = []
        for i in range(model.hidden_range[0], model.hidden_range[1]):
            incoming = torch.matmul(activations, effective_weights[:, i])
            hidden_activations.append(model.activation(incoming).unsqueeze(1))
        
        if hidden_activations:
            hidden_layer = torch.cat(hidden_activations, dim=1).cpu().numpy()
        else:
            print("No hidden layer activations to visualize.")
            return None
    
    # Apply dimensionality reduction
    if method == 'umap':
        try:
            from umap import UMAP
            reducer = UMAP(n_components=2, random_state=42)
            embeddings_2d = reducer.fit_transform(hidden_layer)
            method_name = 'UMAP'
        except ImportError:
            print("UMAP not available. Install with: pip install umap-learn")
            return None
    elif method == 'tsne':
        try:
            from sklearn.manifold import TSNE
            reducer = TSNE(n_components=2, random_state=42)
            embeddings_2d = reducer.fit_transform(hidden_layer)
            method_name = 't-SNE'
        except ImportError:
            print("scikit-learn not available. Install with: pip install scikit-learn")
            return None
    else:
        raise ValueError(f"Unknown method: {method}. Use 'umap' or 'tsne'.")
    
    # Create visualization
    fig, ax = plt.subplots(figsize=(10, 8))
    
    y_np = y.cpu().numpy().flatten()
    scatter = ax.scatter(
        embeddings_2d[:, 0],
        embeddings_2d[:, 1],
        c=y_np,
        cmap='viridis',
        alpha=0.6,
        s=50
    )
    
    plt.colorbar(scatter, ax=ax, label='Target Value')
    ax.set_xlabel(f'{method_name} Component 1')
    ax.set_ylabel(f'{method_name} Component 2')
    
    if title is None:
        title = f'Hidden Layer Embeddings ({method_name})'
    ax.set_title(title)
    
    plt.tight_layout()
    
    if save_path:
        fig.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Embedding visualization saved to: {save_path}")
    elif task_name:
        save_plot(fig, f"{task_name}_embeddings_{method}.png", task_name)
    
    return fig


def create_summary_report(
    model,
    history: Dict,
    final_metrics: Dict,
    task_name: str
):
    """
    Create and save a summary report of training results.
    
    Args:
        model: Trained model
        history: Training history
        final_metrics: Dictionary with final performance metrics
        task_name: Name of the task
    """
    output_dir = ensure_output_dir(task_name)
    report_path = output_dir / f"{task_name}_summary.txt"
    
    with open(report_path, 'w') as f:
        f.write(f"Structure-First Backpropagation - {task_name.upper()} Task\n")
        f.write("=" * 60 + "\n\n")
        f.write(f"Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        
        f.write("Network Configuration:\n")
        f.write(f"  Input nodes: {model.n_input}\n")
        f.write(f"  Hidden nodes: {model.n_hidden}\n")
        f.write(f"  Output nodes: {model.n_output}\n")
        f.write(f"  Total nodes: {model.n_total}\n\n")
        
        f.write("Training Results:\n")
        f.write(f"  Epochs: {len(history['loss'])}\n")
        f.write(f"  Final Loss: {history['loss'][-1]:.4f}\n")
        f.write(f"  Final Sparsity: {history['sparsity'][-1]:.2%}\n")
        f.write(f"  Active Edges: {history['active_edges'][-1]}\n\n")
        
        if final_metrics:
            f.write("Final Performance:\n")
            for key, value in final_metrics.items():
                if isinstance(value, float):
                    f.write(f"  {key}: {value:.4f}\n")
                else:
                    f.write(f"  {key}: {value}\n")
            f.write("\n")
        
        # Structure breakdown
        edges = model.get_structure()
        input_to_hidden = sum(1 for s, t in edges if s < model.n_input and t < model.n_input + model.n_hidden)
        input_to_output = sum(1 for s, t in edges if s < model.n_input and t >= model.n_input + model.n_hidden)
        hidden_to_hidden = sum(1 for s, t in edges if model.n_input <= s < model.n_input + model.n_hidden and model.n_input <= t < model.n_input + model.n_hidden)
        hidden_to_output = sum(1 for s, t in edges if model.n_input <= s < model.n_input + model.n_hidden and t >= model.n_input + model.n_hidden)
        
        f.write("Structure Breakdown:\n")
        f.write(f"  Input → Hidden: {input_to_hidden} edges\n")
        f.write(f"  Input → Output: {input_to_output} edges\n")
        f.write(f"  Hidden → Hidden: {hidden_to_hidden} edges\n")
        f.write(f"  Hidden → Output: {hidden_to_output} edges\n")
    
    print(f"Summary report saved to: {report_path}")


if __name__ == "__main__":
    print("Enhanced visualization module loaded.")
    print("Features:")
    print("  - Interactive visualizations with Plotly")
    print("  - Clustering visualizations (UMAP/t-SNE)")
    print("  - Automated output management")
    print("  - Summary reports")
