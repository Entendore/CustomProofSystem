#!/usr/bin/env python3
import sys
import pytest
import argparse
from pathlib import Path

def main():
    parser = argparse.ArgumentParser(description='Run proof assistant tests')
    parser.add_argument('--folder', default='tests',
                        help='Folder containing tests to run')
    parser.add_argument('--single', help='Run only a specific test file or test function')
    parser.add_argument('--export-dir', default='test_exports',
                        help='Directory for export tests')
    parser.add_argument('--verbose', '-v', action='count', default=0,
                        help='Increase verbosity (use -vv for more detailed output)')
    parser.add_argument('--pdb', action='store_true',
                        help='Drop into debugger on failures')
    parser.add_argument('--coverage', action='store_true',
                        help='Generate coverage report')
    args = parser.parse_args()
    
    # Add project directory to path
    sys.path.insert(0, str(Path(__file__).parent))
    
    # Prepare pytest arguments
    pytest_args = []
    
    # Set verbosity
    if args.verbose:
        pytest_args.extend(['-' + 'v' * args.verbose])
    
    # Set debugger option
    if args.pdb:
        pytest_args.append('--pdb')
    
    # Set coverage option
    if args.coverage:
        pytest_args.extend(['--cov=.', '--cov-report=html', '--cov-report=term'])
    
    # Set export directory
    pytest_args.extend([f'--export-dir={args.export_dir}'])
    
    # Determine which tests to run
    if args.single:
        # Check if it's a file path or test name
        if '::' in args.single:
            # It's a specific test function
            pytest_args.append(args.single)
        else:
            # It's a file
            test_path = Path(args.folder) / args.single
            if not test_path.exists():
                # Try with .py extension
                test_path = test_path.with_suffix('.py')
            
            if not test_path.exists():
                print(f"Error: Test file not found: {test_path}")
                return 1
            
            pytest_args.append(str(test_path))
    else:
        # Run all tests in the folder
        pytest_args.append(args.folder)
    
    print(f"Running tests with arguments: {' '.join(pytest_args)}")
    
    # Run the tests
    result = pytest.main(pytest_args)
    
    # Exit with appropriate code
    sys.exit(result)

if __name__ == "__main__":
    main()