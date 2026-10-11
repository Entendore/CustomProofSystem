import sys

def main():
    # Check for CLI flag
    if "--cli" in sys.argv:
        from app_cli import start_cli
        start_cli()
    else:
        # Default to GUI
        try:
            from PySide6.QtWidgets import QApplication
            from app_gui import ProofAssistantApp
            app = QApplication(sys.argv)
            window = ProofAssistantApp()
            window.show()
            sys.exit(app.exec())
        except ImportError as e:
            print(f"Error loading GUI: {e}")
            print("Please ensure PySide6 is installed: pip install PySide6")
            print("Falling back to CLI...")
            from app_cli import start_cli
            start_cli()

if __name__ == "__main__":
    main()