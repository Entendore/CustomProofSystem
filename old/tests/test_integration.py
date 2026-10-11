import pytest
import os
from pathlib import Path
from proof_assistant import (
    ProofState, ProofTree, parse_formula, process_command
)

class TestProofScriptIntegration:
    """Integration tests for proof script execution"""
    
    @pytest.fixture
    def proof_scripts_dir(self):
        """Path to the proof scripts directory"""
        return Path(__file__).parent / "ProofScripts"
    
    @pytest.fixture
    def export_dir(self, temp_dir):
        """Directory for export tests"""
        export_dir = temp_dir / "export_tests"
        export_dir.mkdir(exist_ok=True)
        return export_dir
    
    def run_script_file(self, script_path):
        """Run a proof script file and return the final state"""
        state = None
        
        with open(script_path, 'r') as f:
            for line in f:
                cmd = line.strip()
                # Skip comments and empty lines
                if not cmd or cmd.startswith('#'):
                    continue
                
                # Process command
                state = process_command(state, cmd)
        
        return state
    
    def test_basic_implication_script(self, proof_scripts_dir):
        """Test running the basic implication proof script"""
        script_path = proof_scripts_dir / "basic_implication.proof"
        assert script_path.exists(), f"Script not found: {script_path}"
        
        state = self.run_script_file(script_path)
        assert state is not None
        assert state.is_complete(), "Proof should be complete"
        assert len(state.proof_tree.steps) == 2, "Should have 2 proof steps"
    
    def test_conjunction_script(self, proof_scripts_dir):
        """Test running the conjunction proof script"""
        script_path = proof_scripts_dir / "conjunction.proof"
        assert script_path.exists(), f"Script not found: {script_path}"
        
        state = self.run_script_file(script_path)
        assert state is not None
        assert state.is_complete(), "Proof should be complete"
        assert len(state.proof_tree.steps) == 5, "Should have 5 proof steps"
    
    def test_quantifiers_script(self, proof_scripts_dir):
        """Test running the quantifier proof script"""
        script_path = proof_scripts_dir / "quantifiers.proof"
        assert script_path.exists(), f"Script not found: {script_path}"
        
        state = self.run_script_file(script_path)
        assert state is not None
        assert state.is_complete(), "Proof should be complete"
    
    def test_double_negation_script(self, proof_scripts_dir):
        """Test running the double negation proof script"""
        script_path = proof_scripts_dir / "double_negation.proof"
        assert script_path.exists(), f"Script not found: {script_path}"
        
        state = self.run_script_file(script_path)
        assert state is not None
        assert state.is_complete(), "Proof should be complete"
    
    def test_equality_script(self, proof_scripts_dir):
        """Test running the equality proof script"""
        script_path = proof_scripts_dir / "equality.proof"
        assert script_path.exists(), f"Script not found: {script_path}"
        
        state = self.run_script_file(script_path)
        assert state is not None
        assert state.is_complete(), "Proof should be complete"
    
    def test_complex_proof_script(self, proof_scripts_dir):
        """Test running the complex proof script"""
        script_path = proof_scripts_dir / "complex_proof.proof"
        assert script_path.exists(), f"Script not found: {script_path}"
        
        state = self.run_script_file(script_path)
        assert state is not None
        assert state.is_complete(), "Proof should be complete"
    
    def test_all_scripts_in_directory(self, proof_scripts_dir):
        """Test all proof scripts in the directory"""
        success_count = 0
        total_count = 0
        
        for script_file in proof_scripts_dir.glob("*.proof"):
            total_count += 1
            print(f"\nTesting {script_file.name}")
            
            try:
                state = self.run_script_file(script_file)
                if state is not None and state.is_complete():
                    success_count += 1
                    print(f"✓ {script_file.name} completed successfully")
                else:
                    print(f"✗ {script_file.name} failed to complete")
                    if state is not None:
                        print(f"Final state: {state}")
            except Exception as e:
                print(f"✗ {script_file.name} crashed: {str(e)}")
        
        print(f"\nTest summary: {success_count}/{total_count} proofs completed")
        assert success_count > 0, "No proofs completed successfully"
        assert success_count == total_count, f"{total_count - success_count} proofs failed"
    
    def test_export_functionality(self, proof_scripts_dir, export_dir):
        """Test export functionality with a completed proof"""
        script_path = proof_scripts_dir / "basic_implication.proof"
        assert script_path.exists(), f"Script not found: {script_path}"
        
        # Run the script
        state = self.run_script_file(script_path)
        assert state is not None
        assert state.is_complete(), "Proof should be complete"
        
        # Set theorem name for export
        state.proof_tree.theorem_name = "test_export_theorem"
        
        # Export to all provers
        export_dir_str = str(export_dir)
        exports = state.proof_tree.export_all(export_dir_str)
        
        # Verify exports
        assert "coq" in exports
        assert "isabelle" in exports
        assert "lean" in exports
        assert len(exports["coq"]) > 0
        assert len(exports["isabelle"]) > 0
        assert len(exports["lean"]) > 0
        
        # Verify files were created
        coq_file = export_dir / "test_export_theorem.v"
        isabelle_file = export_dir / "test_export_theorem.thy"
        lean_file = export_dir / "test_export_theorem.lean"
        
        assert coq_file.exists()
        assert isabelle_file.exists()
        assert lean_file.exists()
        
        # Verify file contents
        with open(coq_file, 'r') as f:
            coq_content = f.read()
            assert "Theorem test_export_theorem" in coq_content
            assert "intros H." in coq_content
            assert "exact H." in coq_content
            assert "Qed." in coq_content
        
        with open(lean_file, 'r') as f:
            lean_content = f.read()
            assert "theorem test_export_theorem" in lean_content
            assert "intro H" in lean_content
            assert "exact H" in lean_content