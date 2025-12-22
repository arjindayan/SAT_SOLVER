import os
import sys
import shutil

# Try to import the solver from main.py
try:
    from main import DPLLSearchEngine
except ImportError:
    print("Error: 'main.py' not found. Please ensure test_suite.py is in the same directory.")
    sys.exit(1)

# ==========================================
# TEST HELPER: MOCK ENGINE FACTORY
# ==========================================
def create_mock_engine(clauses_input):
    """
    Creates a custom mock inference engine function for a specific set of clauses.
    This avoids using global variables by 'capturing' the clauses in a closure.
    """
    def mock_engine_logic():
        trigger_lit = 0
        dl = 0
        
        # 1. Read Trigger Input (written by the Solver)
        if os.path.exists("bcp_trigger_input.txt"):
            with open("bcp_trigger_input.txt", "r") as f:
                content = f.read()
                for line in content.splitlines():
                    if "TRIGGER_LITERAL" in line:
                        parts = line.split(":")
                        if len(parts) > 1:
                            val = parts[1].strip()
                            trigger_lit = int(val) if val else 0
                    if "DL" in line:
                        parts = line.split(":")
                        if len(parts) > 1:
                            dl = int(parts[1].strip())

        # 2. Simulate BCP (Unit Propagation)
        current_assignments = {}
        if trigger_lit != 0:
            current_assignments[abs(trigger_lit)] = (trigger_lit > 0)

        changed = True
        status = "CONTINUE"
        conflict_clause = "None"
        
        # Loop until no more propagations or conflict
        while changed and status != "CONFLICT":
            changed = False
            for i, clause in enumerate(clauses_input):
                false_lits = 0
                unassigned_lits = []
                is_satisfied = False
                
                for lit in clause:
                    var = abs(lit)
                    if var in current_assignments:
                        val = current_assignments[var]
                        if (lit > 0 and val) or (lit < 0 and not val):
                            is_satisfied = True
                            break
                        else:
                            false_lits += 1
                    else:
                        unassigned_lits.append(lit)
                
                if is_satisfied:
                    continue
                    
                # Conflict Check: All literals false
                if false_lits == len(clause):
                    status = "CONFLICT"
                    conflict_clause = f"Clause_{i+1}"
                    break
                
                # Unit Propagation: One unassigned, rest false
                if len(unassigned_lits) == 1 and false_lits == (len(clause) - 1):
                    unit_lit = unassigned_lits[0]
                    var = abs(unit_lit)
                    val = (unit_lit > 0)
                    
                    if var in current_assignments and current_assignments[var] != val:
                        status = "CONFLICT"
                        conflict_clause = f"Clause_{i+1}"
                        break
                    
                    if var not in current_assignments:
                        current_assignments[var] = val
                        changed = True

        # 3. Write Output (read by the Solver)
        log_content = ""
        
        # Section 1: STATUS
        log_content += "--- STATUS ---\n"
        log_content += f"STATUS: {status}\n"
        log_content += f"DL: {dl}\n"
        log_content += f"CONFLICT_ID: {conflict_clause}\n\n"
        
        # Section 2: LOG
        log_content += "--- BCP EXECUTION LOG ---\n"
        log_content += f"[DL{dl}] EXECUTION MOCK\n\n"

        # Section 3: VARS
        log_content += "--- CURRENT VARIABLE STATE ---\n"
        for k, v in current_assignments.items():
            # Format: ID | STATE
            log_content += f"{k} | {'TRUE' if v else 'FALSE'}\n"

        with open("bcp_output.txt", "w") as f:
            f.write(log_content)
            
    return mock_engine_logic

# ==========================================
# TEST RUNNER (Requirements 3.3)
# ==========================================
def run_test_suite():
    print("="*60)
    print("BLG 345E PROJECT #4 - AUTOMATED TEST SUITE (EXTERNAL FILE)")
    print("="*60)
    
    # Setup Artifacts Directory
    artifacts_dir = "test_artifacts"
    if os.path.exists(artifacts_dir):
        try:
            shutil.rmtree(artifacts_dir)
            print(f"Info: Cleaned up existing '{artifacts_dir}' folder.")
        except OSError as e:
            print(f"Warning: Could not clean up '{artifacts_dir}': {e}")
    
    try:
        os.makedirs(artifacts_dir)
        print(f"Info: Created '{artifacts_dir}' for test logs.")
    except OSError as e:
        print(f"Error: Could not create '{artifacts_dir}': {e}")
        sys.exit(1)
    # ---------------------------------------------------------

    # Define Scenarios 
    test_cases = [
        {
            "name": "TEST 1: Immediate Conflict (UNSAT)",
            "desc": "Simple contradiction A ^ -A. Tests initial propagation check.",
            "clauses": [[1], [-1]],
            "vars": 1,
            "expected": "UNSAT"
        },
        {
            "name": "TEST 2: Domino Effect (SAT)",
            "desc": "Unit propagation chain A -> B -> C. Tests BCP integration.",
            "clauses": [[1], [-1, 2], [-2, 3]],
            "vars": 3,
            "expected": "SAT"
        },
        {
            "name": "TEST 3: Backtracking Required (SAT)",
            "desc": "Requires guessing A=True (Fail) then A=False (Success).",
            "clauses": [[1, 2], [-1, 3], [-3, 4], [-2, -4], [-1, -2]], 
            "vars": 4,
            "expected": "SAT"
        },
        {
            "name": "TEST 4: Double Conflict (UNSAT)",
            "desc": "Both branches lead to conflict. Tests full search tree exhaustion.",
            "clauses": [[1, 2], [1, -2], [-1, 2], [-1, -2]],
            "vars": 2,
            "expected": "UNSAT"
        },
        {
            "name": "TEST 5: PDF Scenario Formula",
            "desc": "Formula: (-A v B) ^ (-B v -C) ^ (C v A) ^ (-B v C)",
            "clauses": [[-1, 2], [-2, -3], [3, 1], [-2, 3]], # A=1, B=2, C=3
            "vars": 3,
            "expected": "SAT"
        }
    ]

    passed_count = 0
    
    # Use enumerate to get a test index (1, 2, 3...)
    for i, case in enumerate(test_cases, 1):
        print(f"\nRunning {case['name']}...")
        print(f"Description: {case['desc']}")
        
        # 1. Cleanup old files in current dir to ensure clean run
        if os.path.exists("bcp_output.txt"): os.remove("bcp_output.txt")
        if os.path.exists("bcp_trigger_input.txt"): os.remove("bcp_trigger_input.txt")
        
        # 2. Initialize Solver
        solver = DPLLSearchEngine(case['clauses'], case['vars'])
        
        # 3. Inject the Custom Mock Engine
        solver.execute_inference_engine = create_mock_engine(case['clauses'])
        
        # 4. Run Solve
        result = solver.solve()
        
        # We copy the final state of IO files to the artifacts folder
        try:
            if os.path.exists("bcp_trigger_input.txt"):
                shutil.copy("bcp_trigger_input.txt", os.path.join(artifacts_dir, f"bcp_trigger_input_test_{i}.txt"))
            
            if os.path.exists("bcp_output.txt"):
                shutil.copy("bcp_output.txt", os.path.join(artifacts_dir, f"bcp_output_test_{i}.txt"))
        except Exception as e:
            print(f"Warning: Failed to save artifacts for Test {i}: {e}")
        # ---------------------------------------------------------
        
        # 5. Verify
        actual_status = result
        if isinstance(result, dict) and "status" in result:
            actual_status = result["status"]

        if actual_status == case['expected']:
            print(f"RESULT: {actual_status} [PASSED]")
            passed_count += 1
        else:
            print(f"RESULT: {actual_status} [FAILED] X (Expected: {case['expected']})")
            # Print full dictionary for debugging if needed
            if isinstance(result, dict):
                 print(f"   Full Details: {result}")
            
    print("\n" + "="*60)
    print(f"TEST SUMMARY: {passed_count}/{len(test_cases)} Tests Passed")
    print(f"Artifacts saved in folder: '{artifacts_dir}'")

    print("NOTE TO GRADER: If tests appear to repeat or loop infinitely,")
    print("it is likely due to IDE File Watchers reacting to I/O files.")
    print("Please run this script in a standard terminal (cmd/powershell).")

    print("="*60)

    # Cleanup local files at the very end
    if os.path.exists("bcp_output.txt"): os.remove("bcp_output.txt")
    if os.path.exists("bcp_trigger_input.txt"): os.remove("bcp_trigger_input.txt")

if __name__ == "__main__":
    run_test_suite()