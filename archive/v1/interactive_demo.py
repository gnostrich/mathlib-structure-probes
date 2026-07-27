"""
Interactive Demo for Structure-First Backpropagation

This Streamlit app provides an interactive interface for:
- Uploading custom datasets
- Configuring training parameters
- Training models in real-time
- Visualizing results interactively
"""

import streamlit as st
import torch
import numpy as np
import pandas as pd
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import io

from structure_backprop import StructureBackpropNetwork, train_structure_backprop
from visualization import (
    visualize_structure,
    plot_training_history,
    visualize_embeddings,
    ensure_output_dir
)

# Page configuration
st.set_page_config(
    page_title="Structure-First Backpropagation",
    page_icon="🧠",
    layout="wide"
)

st.title("🧠 Structure-First Backpropagation - Interactive Demo")
st.markdown("""
This interactive tool allows you to experiment with Structure-First Backpropagation,
a novel approach where neural networks learn their own architecture during training.
""")

# Sidebar for configuration
st.sidebar.header("⚙️ Configuration")

# Dataset selection
st.sidebar.subheader("1. Dataset")
dataset_option = st.sidebar.selectbox(
    "Choose Dataset",
    ["XOR Problem", "Addition Problem", "Upload Custom CSV"]
)

# Model configuration
st.sidebar.subheader("2. Model Architecture")
n_input = st.sidebar.number_input("Input Nodes", min_value=1, max_value=10, value=2)
n_hidden = st.sidebar.number_input("Hidden Nodes", min_value=1, max_value=20, value=4)
n_output = st.sidebar.number_input("Output Nodes", min_value=1, max_value=10, value=1)

# Training parameters
st.sidebar.subheader("3. Training Parameters")
n_epochs = st.sidebar.slider("Epochs", min_value=10, max_value=1000, value=300, step=10)
learning_rate = st.sidebar.slider("Learning Rate", min_value=0.001, max_value=0.1, value=0.01, step=0.001, format="%.3f")
rounding_frequency = st.sidebar.slider("Rounding Frequency", min_value=5, max_value=100, value=30, step=5)
rounding_threshold = st.sidebar.slider("Rounding Threshold", min_value=0.1, max_value=0.9, value=0.3, step=0.05, format="%.2f")
rounding_method = st.sidebar.selectbox("Rounding Method", ["threshold", "sigmoid", "hard"])
activation = st.sidebar.selectbox("Activation Function", ["relu", "tanh", "sigmoid"])

# Visualization options
st.sidebar.subheader("4. Visualization Options")
show_embeddings = st.sidebar.checkbox("Show Embeddings (UMAP)", value=True)
embedding_method = st.sidebar.selectbox("Embedding Method", ["umap", "tsne"]) if show_embeddings else None


def create_xor_dataset(n_samples: int = 200):
    """Create XOR dataset."""
    X = []
    y = []
    
    for _ in range(n_samples // 4):
        X.extend([[0, 0], [0, 1], [1, 0], [1, 1]])
        y.extend([[0], [1], [1], [0]])
    
    X = np.array(X, dtype=np.float32)
    X += np.random.randn(*X.shape) * 0.1
    y = np.array(y, dtype=np.float32)
    
    return torch.tensor(X), torch.tensor(y)


def create_addition_dataset(n_samples: int = 200):
    """Create addition dataset: output = input1 + input2."""
    X = torch.randn(n_samples, 2)
    y = X.sum(dim=1, keepdim=True)
    return X, y


# Main content area
col1, col2 = st.columns([1, 2])

with col1:
    st.header("📊 Dataset")
    
    # Load or generate dataset
    X_train, y_train = None, None
    
    if dataset_option == "XOR Problem":
        X_train, y_train = create_xor_dataset(n_samples=200)
        st.info("XOR is a non-linearly separable problem requiring hidden nodes.")
        
    elif dataset_option == "Addition Problem":
        X_train, y_train = create_addition_dataset(n_samples=200)
        st.info("Addition is a linear problem that may learn direct input→output connections.")
        
    elif dataset_option == "Upload Custom CSV":
        uploaded_file = st.file_uploader("Upload CSV file", type=['csv'])
        if uploaded_file:
            df = pd.read_csv(uploaded_file)
            st.write("Preview:", df.head())
            
            # Let user select features and target
            feature_cols = st.multiselect("Select feature columns", df.columns.tolist())
            target_col = st.selectbox("Select target column", df.columns.tolist())
            
            if feature_cols and target_col:
                X_train = torch.tensor(df[feature_cols].values, dtype=torch.float32)
                y_train = torch.tensor(df[target_col].values, dtype=torch.float32).unsqueeze(1)
                n_input = len(feature_cols)
                n_output = 1
    
    if X_train is not None and y_train is not None:
        st.success(f"Dataset loaded: {X_train.shape[0]} samples, {X_train.shape[1]} features")
        
        # Show dataset statistics
        st.subheader("Dataset Statistics")
        st.write(f"Shape: {X_train.shape}")
        st.write(f"Target shape: {y_train.shape}")
        st.write(f"Input range: [{X_train.min():.2f}, {X_train.max():.2f}]")
        st.write(f"Target range: [{y_train.min():.2f}, {y_train.max():.2f}]")

with col2:
    st.header("🎯 Training & Results")
    
    if X_train is not None and y_train is not None:
        if st.button("🚀 Train Model", type="primary"):
            # Create model
            with st.spinner("Creating model..."):
                model = StructureBackpropNetwork(
                    n_input=X_train.shape[1],
                    n_hidden=n_hidden,
                    n_output=y_train.shape[1],
                    rounding_threshold=rounding_threshold,
                    activation=activation
                )
                
                st.write(f"Model created: {model.n_input} input, {model.n_hidden} hidden, {model.n_output} output")
                st.write(f"Initial active edges: {model.get_active_edges()}")
            
            # Training progress
            progress_bar = st.progress(0)
            status_text = st.empty()
            
            # Train model
            with st.spinner("Training model..."):
                history = train_structure_backprop(
                    model=model,
                    train_data=(X_train, y_train),
                    n_epochs=n_epochs,
                    learning_rate=learning_rate,
                    rounding_frequency=rounding_frequency,
                    rounding_method=rounding_method,
                    verbose=False
                )
                
                # Update progress
                for i in range(100):
                    progress_bar.progress(i + 1)
            
            status_text.text("Training complete!")
            
            # Evaluate model
            with torch.no_grad():
                predictions = model(X_train)
                final_loss = torch.nn.functional.mse_loss(predictions, y_train)
                
                if dataset_option == "XOR Problem":
                    accuracy = ((predictions > 0.5) == (y_train > 0.5)).float().mean()
                    st.metric("Accuracy", f"{accuracy.item():.2%}")
            
            st.metric("Final Loss", f"{final_loss.item():.4f}")
            st.metric("Final Sparsity", f"{model.get_sparsity():.2%}")
            st.metric("Active Edges", model.get_active_edges())
            
            # Visualizations
            st.subheader("📈 Training History")
            fig_history = plot_training_history(history, interactive=True)
            st.plotly_chart(fig_history, use_container_width=True)
            
            st.subheader("🔗 Learned Structure")
            fig_structure = visualize_structure(model, interactive=True)
            st.plotly_chart(fig_structure, use_container_width=True)
            
            # Embeddings visualization
            if show_embeddings and n_hidden > 0:
                st.subheader(f"🎨 Hidden Layer Embeddings ({embedding_method.upper()})")
                try:
                    fig_embeddings = visualize_embeddings(
                        model, X_train, y_train, 
                        method=embedding_method
                    )
                    if fig_embeddings:
                        st.pyplot(fig_embeddings)
                except Exception as e:
                    st.warning(f"Could not generate embeddings: {e}")
            
            # Structure summary
            st.subheader("📋 Structure Summary")
            edges = model.get_structure()
            
            input_to_hidden = sum(1 for s, t in edges if s < model.n_input and t < model.n_input + model.n_hidden)
            input_to_output = sum(1 for s, t in edges if s < model.n_input and t >= model.n_input + model.n_hidden)
            hidden_to_hidden = sum(1 for s, t in edges if model.n_input <= s < model.n_input + model.n_hidden and model.n_input <= t < model.n_input + model.n_hidden)
            hidden_to_output = sum(1 for s, t in edges if model.n_input <= s < model.n_input + model.n_hidden and t >= model.n_input + model.n_hidden)
            
            col_a, col_b, col_c, col_d = st.columns(4)
            col_a.metric("Input → Hidden", input_to_hidden)
            col_b.metric("Input → Output", input_to_output)
            col_c.metric("Hidden → Hidden", hidden_to_hidden)
            col_d.metric("Hidden → Output", hidden_to_output)
            
            # Download results
            st.subheader("💾 Export Results")
            
            # Create downloadable history
            history_df = pd.DataFrame(history)
            csv = history_df.to_csv(index=False)
            st.download_button(
                label="Download Training History (CSV)",
                data=csv,
                file_name="training_history.csv",
                mime="text/csv"
            )
    else:
        st.info("👈 Configure settings in the sidebar and load a dataset to begin.")

# Footer
st.markdown("---")
st.markdown("""
### About Structure-First Backpropagation

This algorithm learns neural network architecture during training by:
1. Starting with a fully connected dense graph
2. Using standard backpropagation for continuous learning
3. Periodically rounding weights to binary values {0, 1}
4. Discovering which connections to keep or remove

**Key Benefits:**
- No need to predefine architecture
- Automatically discovers problem-appropriate structures
- Combines continuous optimization with discrete structure learning
""")

st.markdown("**Version 1** | Built with Streamlit")
