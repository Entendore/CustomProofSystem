import sys
import logging
import subprocess
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, 
                               QTextEdit, QLineEdit, QPushButton, QTabWidget, QToolBar, 
                               QStatusBar, QFileDialog, QMessageBox)
from PySide6.QtCore import Qt, QObject
from PySide6.QtGui import QFont, QAction

import proof_core as core

# Custom Logging Handler for GUI
class QTextEditLogger(QObject, logging.Handler):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.widget = QTextEdit()
        self.widget.setReadOnly(True)
        self.widget.setFont(QFont("Courier New", 9))
        self.widget.setStyleSheet("background-color: #1e1e1e; color: #dcdcdc;")

    def emit(self, record):
        msg = self.format(record)
        self.widget.append(msg)

class ProofAssistantApp(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("PyProof Assistant (Logs & Tests Enabled)")
        self.resize(1000, 750)
        
        self.state = None
        
        # Main Layout
        main_widget = QWidget()
        self.setCentralWidget(main_widget)
        layout = QVBoxLayout(main_widget)
        layout.setContentsMargins(5, 5, 5, 5)
        
        # Tabs
        self.tabs = QTabWidget()
        
        # Tab 1: Proof State
        self.goal_display = QTextEdit()
        self.goal_display.setReadOnly(True)
        self.goal_display.setFont(QFont("Courier New", 12))
        self.tabs.addTab(self.goal_display, "Proof State")
        
        # Tab 2: Export Preview
        self.export_view = QTextEdit()
        self.export_view.setReadOnly(True)
        self.tabs.addTab(self.export_view, "Export Preview")
        
        # Tab 3: Logs (New)
        self.log_handler = QTextEditLogger(self)
        self.log_handler.setFormatter(logging.Formatter('%(asctime)s [%(levelname)s] %(message)s'))
        # Add handler to core logger
        core.logger.addHandler(self.log_handler)
        self.tabs.addTab(self.log_handler.widget, "System Logs")
        
        layout.addWidget(self.tabs)
        
        # Input
        input_layout = QHBoxLayout()
        self.cmd_input = QLineEdit()
        self.cmd_input.setFont(QFont("Courier New", 12))
        self.cmd_input.returnPressed.connect(self.execute_command)
        self.cmd_input.setPlaceholderText("Enter command (e.g., intro H, split)")
        
        run_btn = QPushButton("Run")
        run_btn.clicked.connect(self.execute_command)
        
        input_layout.addWidget(self.cmd_input)
        input_layout.addWidget(run_btn)
        layout.addLayout(input_layout)
        
        # Toolbar & Menu
        self.create_toolbar()
        self.create_menu()
        
        # Status
        self.status = QStatusBar()
        self.setStatusBar(self.status)
        self.status.showMessage("Ready. Logging active.")
        
        # Log initial message
        core.logger.info("Application started")

    def create_toolbar(self):
        toolbar = QToolBar("Main")
        self.addToolBar(toolbar)
        
        # Standard Tactics
        for name, cmd in [("Intro", "intro"), ("Split", "split"), ("Left", "left"), ("Right", "right"), ("Assume", "assumption")]:
            btn = QPushButton(name)
            btn.clicked.connect(lambda checked, c=cmd: self.run_tactic(c))
            toolbar.addWidget(btn)
            
        toolbar.addSeparator()
        
        # Test Button (New)
        test_btn = QPushButton("🧪 Run Tests")
        test_btn.setStyleSheet("background-color: #4CAF50; color: white; font-weight: bold;")
        test_btn.clicked.connect(self.run_tests)
        toolbar.addWidget(test_btn)

    def create_menu(self):
        menu = self.menuBar()
        file_menu = menu.addMenu("File")
        
        export_act = QAction("Export to Coq", self)
        export_act.triggered.connect(lambda: self.export_proof("coq"))
        file_menu.addAction(export_act)
        
        file_menu.addSeparator()
        exit_act = QAction("Exit", self)
        exit_act.triggered.connect(self.close)
        file_menu.addAction(exit_act)
        
        tools_menu = menu.addMenu("Tools")
        test_act = QAction("Run Unit Tests", self)
        test_act.triggered.connect(self.run_tests)
        tools_menu.addAction(test_act)

    def run_tactic(self, cmd: str):
        self.cmd_input.setText(cmd)
        self.execute_command()

    def execute_command(self):
        text = self.cmd_input.text().strip()
        if not text: return
        
        core.logger.info(f"User command: {text}")
        self.state, msg = core.process_command(self.state, text)
        
        self.update_display()
        self.status.showMessage(msg.split('\n')[0])
        
        if "Proof complete" in msg:
            QMessageBox.information(self, "Success", "Proof Complete!")
            core.logger.info("Proof completed successfully.")
            
        self.cmd_input.clear()

    def update_display(self):
        if not self.state:
            self.goal_display.setText("No active proof.")
            return
        
        self.goal_display.setText(str(self.state))

    def export_proof(self, fmt: str):
        if not self.state or not self.state.proof_tree.initial_goal:
            QMessageBox.warning(self, "Error", "No proof to export.")
            return
            
        code = self.state.proof_tree.export_coq() if fmt == 'coq' else ""
        self.export_view.setText(code)
        self.tabs.setCurrentIndex(1)
        
        path, _ = QFileDialog.getSaveFileName(self, "Save File", "", "Text Files (*.v)")
        if path:
            with open(path, "w") as f: f.write(code)
            self.status.showMessage(f"Exported to {path}")

    def run_tests(self):
        """Executes the test suite and displays output in the GUI."""
        core.logger.info("Running tests...")
        self.status.showMessage("Running tests...")
        
        try:
            # Run pytest via subprocess to capture output cleanly
            result = subprocess.run(
                [sys.executable, "-m", "pytest", "tests", "-v"], 
                capture_output=True, text=True, cwd="."
            )
            
            output = result.stdout + "\n" + result.stderr
            
            # Show output in Export/Preview tab
            self.export_view.setText(f"--- Test Results ---\n{output}")
            self.tabs.setCurrentIndex(1) # Switch to output tab
            
            if result.returncode == 0:
                QMessageBox.information(self, "Tests Passed", "All tests passed successfully!")
                core.logger.info("Tests passed.")
            else:
                QMessageBox.warning(self, "Tests Failed", "Some tests failed. See output for details.")
                core.logger.warning("Tests failed.")
                
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to run tests: {e}")
            core.logger.error(f"Test execution error: {e}")

if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = ProofAssistantApp()
    window.show()
    sys.exit(app.exec())