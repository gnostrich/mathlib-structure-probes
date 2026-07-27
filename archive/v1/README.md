# Structure-First Backpropagation - Version 1

This is the initial implementation of Structure-First Backpropagation based on the project concept, now enhanced with advanced visualization capabilities, interactive dashboards, and automated output management.

## Overview

Version 1 implements the core algorithm with extensive visualization features:
- Train a dense directed graph with standard backprop
- Interleave discrete rounding steps that snap weights to {0, 1}
- Learn network structure during training (no predefined architecture)
- **NEW:** Interactive dashboards for real-time exploration
- **NEW:** Advanced visualizations with UMAP/t-SNE embeddings
- **NEW:** Automated output management and reporting

## Implementation Files

1. **ARCHITECTURE.md** - Visual representation of the Structure-First Backpropagation concept
   - Dense graph initialization diagrams
   - Training loop phases (continuous + discrete)
   - Information flow and structure emergence
   
2. **TRAINING_PSEUDOCODE.md** - Detailed algorithmic description
   - Main training loop with alternating phases
   - Forward/backward pass subroutines
   - Weight rounding methods (threshold, sigmoid, hard)
   - Variants and extensions

3. **structure_backprop.py** - Working PyTorch implementation
   - `StructureBackpropNetwork` class
   - Dense directed graph initialization
   - Configurable rounding methods
   - Structure metrics and extraction

4. **example.py** - Demonstrations on two tasks
   - XOR problem (non-linear, requires hidden nodes)
   - Addition problem (linear, can use direct connections)
   - Visualizations and training history
   - **NEW:** Automated output saving to organized folders
   - **NEW:** Embedding visualizations with UMAP

5. **visualization.py** - Enhanced visualization module (**NEW**)
   - Interactive Plotly visualizations
   - UMAP/t-SNE clustering for embeddings
   - Automated output management
   - Summary report generation

6. **interactive_demo.py** - Streamlit dashboard (**NEW**)
   - Real-time model training
   - Custom dataset upload
   - Adjustable training parameters
   - Interactive result visualization

## Quick Start

### Installation

Install dependencies:
```bash
pip install -r requirements.txt
```

### Running the Demos

**Basic Demo (Command Line):**
```bash
python example.py
```

This will train the Structure-First Backpropagation network on two tasks:
- **XOR Problem**: Non-linear task requiring hidden nodes
- **Addition Problem**: Linear task that can use direct connections

All outputs (plots, embeddings, summaries) are automatically saved to:
- `outputs/v1/xor/` - XOR problem results
- `outputs/v1/addition/` - Addition problem results

**Interactive Dashboard:**
```bash
streamlit run interactive_demo.py
```

This launches a web interface where you can:
- Choose from preset datasets or upload your own CSV
- Adjust training parameters in real-time
- Visualize results interactively
- Export training history and metrics

The demo shows how the network learns which connections to keep (weight=1) or remove (weight=0) through training.

## Key Features

- **Dense Graph Initialization**: Starts with fully connected network
- **Gradient-Based Learning**: Uses standard backpropagation
- **Structure Discovery**: Periodic weight rounding to {0, 1} discovers sparse topology
- **No Predefined Architecture**: Network learns its own structure
- **Interactive Visualization**: Real-time exploration with Streamlit/Plotly (**NEW**)
- **Embedding Analysis**: UMAP/t-SNE visualizations of learned representations (**NEW**)
- **Automated Outputs**: All results automatically saved and organized (**NEW**)
- **Custom Datasets**: Upload and train on your own data (**NEW**)

## Usage Example

### Basic Usage

```python
from structure_backprop import StructureBackpropNetwork, train_structure_backprop
from visualization import visualize_structure, plot_training_history, visualize_embeddings
import torch

# Create network
model = StructureBackpropNetwork(
    n_input=2,
    n_hidden=4,
    n_output=1,
    rounding_threshold=0.3
)

# Prepare data
X = torch.randn(100, 2)
y = torch.randn(100, 1)

# Train
history = train_structure_backprop(
    model=model,
    train_data=(X, y),
    n_epochs=100,
    learning_rate=0.01,
    rounding_frequency=10
)

# Inspect learned structure
print(f"Sparsity: {model.get_sparsity():.2%}")
print(f"Active edges: {model.get_active_edges()}")
edges = model.get_structure()
```

### Advanced Visualization

```python
# Static visualization with automatic saving
visualize_structure(
    model, 
    title="My Model Structure",
    task_name="my_task"  # Saves to outputs/v1/my_task/
)

# Interactive Plotly visualization
fig = visualize_structure(
    model,
    interactive=True
)
fig.show()

# Plot training history
plot_training_history(
    history,
    task_name="my_task",
    interactive=True  # Use Plotly for interactivity
)

# Visualize embeddings with UMAP
visualize_embeddings(
    model, 
    X, 
    y,
    method='umap',  # or 'tsne'
    task_name="my_task"
)
```

### Custom Dataset Training

```python
import pandas as pd

# Load your data
df = pd.read_csv("my_data.csv")
X = torch.tensor(df[['feature1', 'feature2']].values, dtype=torch.float32)
y = torch.tensor(df['target'].values, dtype=torch.float32).unsqueeze(1)

# Create and train model
model = StructureBackpropNetwork(
    n_input=X.shape[1],
    n_hidden=5,
    n_output=1
)

history = train_structure_backprop(
    model=model,
    train_data=(X, y),
    n_epochs=200,
    learning_rate=0.01
)

# Visualize results
visualize_structure(model, task_name="custom_task")
plot_training_history(history, task_name="custom_task")
```

## Results

The v1 implementation successfully demonstrates structure learning:

**XOR Problem (Non-linear):**
- Network: 2 inputs → 4 hidden → 1 output
- Started with 30 edges (fully connected)
- Learned structure with 14 edges (53% sparsity)
- Final accuracy: 74.5%
- Network discovers it needs hidden nodes for non-linear task

**Addition Problem (Linear):**
- Network: 2 inputs → 3 hidden → 1 output
- Started with 20 edges (fully connected)
- Learned structure with 11 edges (45% sparsity)
- Final MSE loss: 0.378
- Network learns direct input→output connections

## Output Organization

All demo outputs are automatically saved to organized folders:

```
v1/
├── outputs/
│   └── v1/
│       ├── xor/
│       │   ├── xor_structure.png           # Structure heatmap
│       │   ├── xor_history.png             # Training metrics
│       │   ├── xor_embeddings_umap.png     # UMAP visualization
│       │   ├── xor_structure_interactive.html  # Interactive structure
│       │   ├── xor_history_interactive.html    # Interactive metrics
│       │   └── xor_summary.txt             # Text summary report
│       └── addition/
│           ├── addition_structure.png
│           ├── addition_history.png
│           ├── addition_embeddings_umap.png
│           ├── addition_structure_interactive.html
│           ├── addition_history_interactive.html
│           └── addition_summary.txt
```

Each output folder contains:
- **Structure visualizations**: Both static PNG and interactive HTML
- **Training history plots**: Loss, sparsity, and edge count over time
- **Embedding visualizations**: UMAP or t-SNE of hidden layer activations
- **Summary reports**: Text file with key metrics and statistics

## Visualization Features

### 1. Structure Heatmaps
- Color-coded weight matrices showing learned connections
- Clear separation of node types (input, hidden, output)
- Interactive tooltips with exact weight values (Plotly version)

### 2. Training History
- Loss curves showing convergence
- Sparsity evolution over epochs
- Active edge count dynamics
- Interactive zoom and pan (Plotly version)

### 3. Embedding Visualizations
- UMAP or t-SNE projections of hidden layer activations
- Color-coded by target values
- Reveals learned representations and clustering

### 4. Interactive Dashboard
The Streamlit dashboard (`interactive_demo.py`) provides:
- **Dataset Management**: Upload CSV files or use preset datasets
- **Parameter Tuning**: Adjust all training hyperparameters
- **Real-time Training**: Watch metrics update during training
- **Export Options**: Download training history and results

## Files

- `ARCHITECTURE.md` - Detailed architecture diagrams and information flow
- `TRAINING_PSEUDOCODE.md` - Step-by-step algorithmic pseudocode
- `structure_backprop.py` - Core implementation
- `example.py` - Demonstration scripts with visualizations
- `visualization.py` - Enhanced visualization module (**NEW**)
- `interactive_demo.py` - Streamlit interactive dashboard (**NEW**)
- `requirements.txt` - Python dependencies
- `.gitignore` - Excludes output files and artifacts

## Interactive Dashboard Guide

### Launching the Dashboard

```bash
streamlit run interactive_demo.py
```

The dashboard will open in your browser at `http://localhost:8501`

### Using the Dashboard

1. **Select Dataset** (Sidebar):
   - Choose from XOR or Addition presets
   - Or upload your own CSV file

2. **Configure Model** (Sidebar):
   - Set number of input, hidden, and output nodes
   - Choose activation function (relu, tanh, sigmoid)

3. **Set Training Parameters** (Sidebar):
   - Epochs: Number of training iterations
   - Learning Rate: Step size for gradient descent
   - Rounding Frequency: How often to round weights
   - Rounding Threshold: Cutoff for binary rounding
   - Rounding Method: threshold, sigmoid, or hard

4. **Train Model**:
   - Click "Train Model" button
   - Watch real-time progress
   - View interactive visualizations

5. **Explore Results**:
   - Training history with zoom/pan
   - Interactive structure heatmap
   - Embedding visualizations
   - Download training history as CSV

### Custom Dataset Format

Upload CSV files with:
- Feature columns: Input variables
- Target column: Output variable to predict

Example CSV:
```csv
feature1,feature2,feature3,target
1.0,2.0,3.0,6.0
2.0,3.0,4.0,9.0
...
```

## Tips and Best Practices

### Training Parameters

- **Learning Rate**: Start with 0.01, increase for faster convergence, decrease if unstable
- **Rounding Frequency**: Higher values (50-100) allow more continuous learning between rounding steps
- **Rounding Threshold**: Lower values (0.2-0.3) create sparser networks
- **Hidden Nodes**: Start with 2-4x input nodes for non-linear problems

### Interpreting Results

- **High Sparsity**: Network found efficient structure (good!)
- **Low Sparsity**: Problem may be complex or need more training
- **Direct Input→Output**: Suggests linear relationships
- **Active Hidden Nodes**: Indicates non-linear feature learning

### Visualization Tips

- Use **interactive visualizations** for detailed exploration
- Check **embedding plots** to understand learned representations
- Monitor **training history** for convergence issues
- Review **summary reports** for quick overview

## Future Versions

This v1 implementation serves as a baseline. Future versions (v2, v3, etc.) will incorporate improvements and refinements based on review and experimentation.
