#!/usr/bin/env python3
import sys
import pytest
import argparse
from pathlib import Path

def main():
    parser = argparse.ArgumentParser(description='Run proof assistant tests')
    parser.add_argument('--verbose', '-v', action='count', default=0)
    args = parser.parse_args()
    
    # Add project directory to path
    sys.path.insert(0, str(Path(__file__).parent))
    
    pytest_args = ["tests"]
    if args.verbose:
        pytest_args.extend(['-' + 'v' * args.verbose])
        
    sys.exit(pytest.main(pytest_args))

if __name__ == "__main__":
    main()