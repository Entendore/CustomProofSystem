import streamlit as st
import json
import os
from datetime import datetime
from pathlib import Path
from copy import deepcopy

# Import all the necessary components from the original code
# (In a real implementation, we would import or copy the entire codebase)
# For this example, I'll outline the structure with placeholders for the actual functions

# Session state initialization
if 'proof_state' not in st.session_state:
    st.session_state.proof_state = None
if 'history' not in st.session_state:
    st.session_state.history = []
if 'theorem_name' not in st.session_state:
    st.session_state.theorem_name = "theorem"
if 'current_goal' not in st.session_state:
    st.session_state.current_goal = ""
if 'last_command' not in st.session_state:
    st.session_state.last_command = ""
if 'command_history' not in st.session_state:
    st.session_state.command_history = []

def setup_page():
    st.set_page_config(
        page_title="Interactive Proof Assistant",
        page_icon="🔍",
        layout="wide",
        initial_sidebar_state="expanded"
    )
    st.title("🔍 Interactive Proof Assistant")
    st.markdown("A web interface for formal theorem proving with export to Coq, Isabelle, and Lean")

def get_proof_state_display():
    """Generate a formatted display of the current proof state"""
    if st.session_state.proof_state is None:
        return "No active proof. Set a goal to begin."
    
    if st.session_state.proof_state.is_complete():
        return "✅ **Proof complete!** Use the Export tab to export your proof."
    
    return str(st.session_state.proof_state)

def apply_tactic(tactic_name, args=None):
    """Apply a tactic to the current proof state"""
    try:
        # This would call the actual tactic functions from the original code
        # For demonstration, I'm showing the structure
        old_state = deepcopy(st.session_state.proof_state)
        st.session_state.command_history.append(f"{tactic_name} {args if args else ''}".strip())
        
        # Process the command (this would call process_command from the original code)
        st.session_state.proof_state = process_command(st.session_state.proof_state, f"{tactic_name} {args if args else ''}".strip())
        
        # Record successful action for undo
        st.session_state.history.append({
            'action': tactic_name,
            'args': args,
            'state': old_state
        })
        
        st.success(f"Applied tactic: {tactic_name}")
        return True
    except Exception as e:
        st.error(f"Error applying tactic: {str(e)}")
        return False

def undo_last_action():
    """Undo the last tactic application"""
    if not st.session_state.history:
        st.warning("No actions to undo")
        return
    
    last_action = st.session_state.history.pop()
    st.session_state.proof_state = last_action['state']
    st.success(f"Undid action: {last_action['action']}")

def main_interface():
    setup_page()
    
    # Sidebar navigation
    tab = st.sidebar.radio("Navigation", ["Proof Workspace", "Tactics", "Export", "History"])
    
    # Main content based on tab selection
    if tab == "Proof Workspace":
        workspace_tab()
    elif tab == "Tactics":
        tactics_tab()
    elif tab == "Export":
        export_tab()
    elif tab == "History":
        history_tab()
    
    # Display current proof state at the bottom
    st.markdown("---")
    st.subheader("Current Proof State")
    state_display = get_proof_state_display()
    
    # Use different styling based on proof status
    if "✅ Proof complete!" in state_display:
        st.success(state_display)
    else:
        st.code(state_display, language="text")

def workspace_tab():
    st.header("Proof Workspace")
    
    # Goal setting section
    st.subheader("Set Initial Goal")
    col1, col2 = st.columns([3, 1])
    with col1:
        goal_input = st.text_input("Logical formula", placeholder="forall x. P(x) -> Q(x)", key="goal_input")
    with col2:
        theorem_name = st.text_input("Theorem name", value=st.session_state.theorem_name, key="theorem_name_input")
        st.session_state.theorem_name = theorem_name
    
    if st.button("SetBranch Goal", type="primary"):
        if goal_input.strip():
            # This would process the goal command from the original code
            st.session_state.proof_state = process_command(None, f"goal {goal_input}")
            st.success(f"Goal set: {goal_input}")
        else:
            st.warning("Please enter a formula")
    
    # Current goal display and hints
    if st.session_state.proof_state and not st.session_state.proof_state.is_complete():
        st.subheader("Proof Hints")
        # This would call the hint function from the original code
        with st.expander("Show hints for current goal"):
            hints = tactic_hint(st.session_state.proof_state)
            st.write(hints if hints else "No specific hints available for this goal.")

def tactics_tab():
    st.header("Apply Tactics")
    
    if st.session_state.proof_state is None:
        st.warning("No active proof. Set a goal first.")
        return
    
    if st.session_state.proof_state.is_complete():
        st.success("Proof is already complete! Visit the Export tab to export your proof.")
        return
    
    # Get current goal context for smart tactic suggestions
    current = st.session_state.proof_state.current()
    goal_type = "unknown"
    if current:
        _, goal = current
        if isinstance(goal, tuple):
            goal_type = goal[0]
    
    # Organize tactics by goal type
    st.subheader("Available Tactics")
    
    # Common tactics section
    with st.expander("Basic Tactics", expanded=True):
        col1, col2, col3 = st.columns(3)
        with col1:
            if st.button("intro", help="Introduce implication or universal quantifier"):
                apply_tactic("intro")
            if st.button("exact", help="Solve with exact hypothesis match"):
                exact_target = st.text_input("Hypothesis name or formula", key="exact_input")
                if exact_target and st.button("Apply exact", key="apply_exact"):
                    apply_tactic("exact", exact_target)
        
        with col2:
            if st.button("split", help="Split conjunction goal"):
                apply_tactic("split")
            if st.button("assumption", help="Solve if goal matches hypothesis"):
                apply_tactic("assumption")
        
        with col3:
            if st.button("auto", help="Attempt automatic proof"):
                depth = st.slider("Search depth", 1, 5, 3, key="auto_depth")
                if st.button("Apply auto", key="apply_auto"):
                    apply_tactic("auto", str(depth))
    
    # Context-dependent tactics
    with st.expander("Context-Dependent Tactics", expanded=False):
        # This section would show tactics that depend on current goal type
        if goal_type == "or":
            st.subheader("Disjunction Goal (∨)")
            col1, col2 = st.columns(2)
            with col1:
                if st.button("left", help="Solve left disjunct"):
                    apply_tactic("left")
            with col2:
                if st.button("right", help="Solve right disjunct"):
                    apply_tactic("right")
        
        # More context-dependent tactics would be added here...
    
    # Undo/Redo section
    st.markdown("---")
    st.subheader("Proof Navigation")
    col1, col2 = st.columns(2)
    with col1:
        if st.button("↩️ Undo", help="Undo last tactic", type="secondary"):
            undo_last_action()
    with col2:
        if st.button("↪️ Redo", help="Redo last undone tactic", type="secondary"):
            # Redo functionality would be implemented here
            st.warning("Redo functionality not yet implemented in this demo")

def export_tab():
    st.header("Export Proof")
    
    if st.session_state.proof_state is None:
        st.warning("No active proof to export.")
        return
    
    if not st.session_state.proof_state.proof_tree.initial_goal:
        st.warning("No initial goal set. Set a goal first.")
        return
    
    # Export options
    st.subheader("Export Options")
    col1, col2 = st.columns(2)
    
    with col1:
        export_system = st.selectbox("Target System", ["All", "Coq", "Isabelle", "Lean"])
        export_dir = st.text_input("Export Directory", value="exports")
    
    with col2:
        if st.button("Export Proof", type="primary"):
            try:
                # Create export directory if it doesn't exist
                Path(export_dir).mkdir(parents=True, exist_ok=True)
                
                # Set theorem name in proof tree
                st.session_state.proof_state.proof_tree.theorem_name = st.session_state.theorem_name
                
                # Perform export
                if export_system == "All":
                    exports = st.session_state.proof_state.proof_tree.export_all(export_dir)
                    st.success("Exported to all theorem provers:")
                    for system, code in exports.items():
                        if code:
                            st.code(f"{system.upper()}: {len(code.splitlines())} lines", language="text")
                else:
                    # Export to specific system
                    if export_system == "Coq":
                        code = st.session_state.proof_state.proof_tree.export_coq()
                    elif export_system == "Isabelle":
                        code = st.session_state.proof_state.proof_tree.export_isabelle()
                    elif export_system == "Lean":
                        code = st.session_state.proof_state.proof_tree.export_lean()
                    
                    if code:
                        st.subheader(f"{export_system} Code")
                        st.code(code, language="coq" if export_system == "Coq" else "isabelle" if export_system == "Isabelle" else "lean")
                        
                        # Provide download button
                        filename = f"{st.session_state.theorem_name.lower()}.{('v' if export_system == 'Coq' else 'thy' if export_system == 'Isabelle' else 'lean')}"
                        st.download_button(
                            label=f"Download {export_system} file",
                            data=code,
                            file_name=filename,
                            mime="text/plain"
                        )
            except Exception as e:
                st.error(f"Export failed: {str(e)}")
    
    # Proof summary
    st.markdown("---")
    st.subheader("Proof Summary")
    if st.session_state.proof_state.proof_tree.steps:
        st.session_state.proof_state.proof_tree.pretty_print()
        # The pretty_print method would need to be adapted to return a string for Streamlit

def history_tab():
    st.header("Proof History")
    
    if not st.session_state.command_history:
        st.info("No commands executed yet.")
        return
    
    st.subheader("Command History")
    for i, cmd in enumerate(reversed(st.session_state.command_history[-10:]), 1):
        st.text(f"{i}. {cmd}")
    
    st.markdown("---")
    st.subheader("Full Proof Script")
    script_content = "# Proof script generated by Interactive Proof Assistant\n"
    script_content += f"# Theorem: {st.session_state.theorem_name}\n"
    script_content += f"# Generated on: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n"
    
    for cmd in st.session_state.command_history:
        if cmd.startswith("goal"):
            script_content += f"{cmd}\n"
        elif not cmd.startswith(("state", "context", "hint", "explain", "proof")):
            script_content += f"{cmd}\n"
    
    st.code(script_content, language="text")
    
    st.download_button(
        label="Download Proof Script",
        data=script_content,
        file_name=f"{st.session_state.theorem_name.lower()}_proof.script",
        mime="text/plain"
    )

if __name__ == "__main__":
    main_interface()