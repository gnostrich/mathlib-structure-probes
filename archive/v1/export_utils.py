import json
import torch
import matplotlib.pyplot as plt
from pathlib import Path

def ensure_output_dir(task_name='default'):
    """Create outputs folder structure for a task"""
    output_dir = Path('outputs') / task_name
    output_dir.mkdir(parents=True, exist_ok=True)
    return output_dir

def save_training_plot(history, task_name, output_dir=None):
    """Save training history as PNG"""
    if output_dir is None:
        output_dir = ensure_output_dir(task_name)
    
    plt.figure(figsize=(10, 6))
    plt.plot(history['loss'])
    plt.xlabel('Epoch')
    plt.ylabel('Loss')
    plt.title(f'{task_name.capitalize()} - Training History')
    plt.grid(True)
    
    path = output_dir / 'training_history.png'
    plt.savefig(path, dpi=150, bbox_inches='tight')
    plt.close()
    return path

def save_metrics(metrics, task_name, output_dir=None):
    """Save metrics summary as JSON"""
    if output_dir is None:
        output_dir = ensure_output_dir(task_name)
    
    # Convert torch tensors to python scalars for JSON
    metrics_serializable = {}
    for k, v in metrics.items():
        if isinstance(v, torch.Tensor):
            metrics_serializable[k] = v.item()
        else:
            metrics_serializable[k] = v
    
    path = output_dir / 'metrics.json'
    with open(path, 'w') as f:
        json.dump(metrics_serializable, f, indent=2)
    return path

def create_outputs_readme(task_names):
    """Create README for outputs folder"""
    output_dir = Path('outputs')
    output_dir.mkdir(exist_ok=True)
    
    readme_content = f"""# Training Outputs

Generated outputs from Structure-Backprop training.

## Tasks

{chr(10).join(f'- {name}' for name in task_names)}

## Files

Each task folder contains:
- `training_history.png`: Training loss curve
- `metrics.json`: Final metrics (loss, sparsity, etc.)

## Usage

Load metrics:
```python
import json
with open('outputs/[task]/metrics.json') as f:
    metrics = json.load(f)
```

View plots in any image viewer.
"""
    
    path = output_dir / 'README.md'
    with open(path, 'w') as f:
        f.write(readme_content)
    return path
