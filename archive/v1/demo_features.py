"""
Quick Demo: Structure-First Backpropagation Enhanced Features

This script demonstrates the new visualization and automation features
added to the v1 implementation.
"""

import torch
import numpy as np
from structure_backprop import StructureBackpropNetwork, train_structure_backprop
from visualization import (
    visualize_structure,
    plot_training_history,
    visualize_embeddings,
    create_summary_report
)

print("="*70)
print("STRUCTURE-FIRST BACKPROPAGATION - ENHANCED FEATURES DEMO")
print("="*70)

# Set random seed
torch.manual_seed(42)
np.random.seed(42)

# Create XOR dataset
print("\n1. Creating XOR dataset...")
X = torch.tensor([[0, 0], [0, 1], [1, 0], [1, 1]], dtype=torch.float32)
y = torch.tensor([[0], [1], [1], [0]], dtype=torch.float32)
# Replicate for more samples
X = X.repeat(25, 1)
y = y.repeat(25, 1)
print(f"   Dataset: {X.shape[0]} samples, {X.shape[1]} features")

# Create model
print("\n2. Creating model...")
model = StructureBackpropNetwork(
    n_input=2,
    n_hidden=4,
    n_output=1,
    rounding_threshold=0.3,
    activation='relu'
)
print(f"   Model: {model.n_input} input, {model.n_hidden} hidden, {model.n_output} output")
print(f"   Initial edges: {model.get_active_edges()}")

# Train model
print("\n3. Training model...")
history = train_structure_backprop(
    model=model,
    train_data=(X, y),
    n_epochs=200,
    learning_rate=0.01,
    rounding_frequency=20,
    verbose=False
)
print(f"   Training complete!")
print(f"   Final loss: {history['loss'][-1]:.4f}")
print(f"   Final sparsity: {model.get_sparsity():.2%}")
print(f"   Final edges: {model.get_active_edges()}")

# Evaluate
with torch.no_grad():
    predictions = model(X)
    accuracy = ((predictions > 0.5) == (y > 0.5)).float().mean()
print(f"   Accuracy: {accuracy:.2%}")

print("\n4. Generating visualizations...")

# Static visualizations
print("   - Creating structure heatmap...")
visualize_structure(model, title="XOR - Learned Structure", task_name="demo")

print("   - Creating training history plot...")
plot_training_history(history, title="XOR - Training History", task_name="demo")

print("   - Creating UMAP embedding visualization...")
try:
    visualize_embeddings(model, X, y, method='umap', task_name="demo")
except ImportError as e:
    print(f"     UMAP not available: {e}")

# Interactive visualizations
print("\n5. Generating interactive visualizations...")
print("   - Creating interactive structure heatmap...")
try:
    visualize_structure(model, title="XOR - Interactive Structure", 
                       task_name="demo", interactive=True)
except ImportError as e:
    print(f"     Plotly not available: {e}")

print("   - Creating interactive training history...")
try:
    plot_training_history(history, title="XOR - Interactive History",
                         task_name="demo", interactive=True)
except ImportError as e:
    print(f"     Plotly not available: {e}")

# Summary report
print("\n6. Creating summary report...")
final_metrics = {
    'accuracy': accuracy.item(),
    'final_loss': history['loss'][-1]
}
create_summary_report(model, history, final_metrics, "demo")

print("\n" + "="*70)
print("DEMO COMPLETE!")
print("="*70)
print("\nAll outputs saved to: outputs/v1/demo/")
print("\nGenerated files:")
print("  - demo_structure.png              (static structure visualization)")
print("  - demo_history.png                (static training history)")
print("  - demo_embeddings_umap.png        (UMAP embedding visualization)")
print("  - demo_structure_interactive.html (interactive structure)")
print("  - demo_history_interactive.html   (interactive training history)")
print("  - demo_summary.txt                (text summary report)")
print("\nTo launch the interactive dashboard, run:")
print("  streamlit run interactive_demo.py")
print("="*70)
