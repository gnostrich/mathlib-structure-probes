import torch
import numpy as np
from sklearn.model_selection import train_test_split as sklearn_split

def set_seed(seed: int):
    """Set random seeds for reproducibility across all libraries"""
    torch.manual_seed(seed)
    np.random.seed(seed)

def train_val_test_split(X, y, train_size=0.6, val_size=0.2, test_size=0.2, random_state=None):
    """Split data into train/val/test sets with no overlap."""
    assert abs(train_size + val_size + test_size - 1.0) < 1e-6
    X_train, X_temp, y_train, y_temp = sklearn_split(X, y, train_size=train_size, random_state=random_state)
    val_ratio = val_size / (val_size + test_size)
    X_val, X_test, y_val, y_test = sklearn_split(X_temp, y_temp, train_size=val_ratio, random_state=random_state)
    return X_train, X_val, X_test, y_train, y_val, y_test
