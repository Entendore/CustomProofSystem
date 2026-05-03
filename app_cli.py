import proof_core as core
import sys

def start_cli():
    print("PyProof CLI Assistant")
    print("Type 'help' for commands, 'exit' to quit.")
    
    state = None
    
    while True:
        try:
            cmd = input("PyProof > ").strip()
            if not cmd:
                continue
                
            if cmd.lower() in ["exit", "quit"]:
                print("Goodbye.")
                break
                
            if cmd.lower() == "help":
                print("Available commands:")
                print("  goal <formula>      - Set a new goal to prove")
                print("  theorem <name> <f>  - Set a theorem to prove")
                print("  intro <name>        - Introduce implication or forall")
                print("  exact <term>        - Prove goal exactly using term/hypothesis")
                print("  split               - Split a conjunction goal")
                print("  left / right        - Prove left/right of a disjunction")
                print("  assumption          - Prove goal using an exact hypothesis match")
                print("  undo / redo         - Navigate proof history")
                print("  exit                - Exit the assistant")
                continue

            # Process command using core logic
            state, msg = core.process_command(state, cmd)
            print("-" * 40)
            print(msg)
            
            # Print current state if not complete
            if state and not state.is_complete():
                print(str(state))
            elif state and state.is_complete():
                print("Proof is complete. Use 'goal' to start a new one.")
            
            print("-" * 40)

        except KeyboardInterrupt:
            print("\nExiting.")
            break
        except Exception as e:
            print(f"Fatal Error: {e}")

if __name__ == "__main__":
    start_cli()