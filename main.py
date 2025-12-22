import os
import random

# ==========================================
# BÖLÜM 1: MOCK INFERENCE ENGINE (SİMÜLASYON)
# ==========================================
def mock_inference_engine_generic():
    """
    Bu fonksiyon, C++ Inference Engine'in (BCP) yaptığı işi Python ile taklit eder.
    Dosyadan Trigger okur -> Clause'lara bakar -> Unit Propagation yapar -> Dosyaya yazar.
    """
    trigger_lit = 0
    dl = 0
    
    # 1. Trigger Dosyasını Oku
    if os.path.exists("bcp_trigger_input.txt"):
        with open("bcp_trigger_input.txt", "r") as f:
            content = f.read()
            for line in content.splitlines():
                line = line.strip()
                if line.startswith("#"):
                    continue
                if "TRIGGER_LITERAL" in line:
                    val = line.split(":")[1].strip()
                    trigger_lit = int(val) if val else 0
                elif line.startswith("DL"):
                    dl = int(line.split(":")[1].strip())

    # Global 'clauses' listesini kullanacağız (Main bloğundan gelir)
    global clauses 
    
    # Geçici atama sözlüğü (Simülasyon için anlık durumu tutar)
    current_assignments = {} 
    
    # Eğer Trigger 0 değilse (yani bir karar verilmişse), bunu atayarak başla
    if trigger_lit != 0:
        current_assignments[abs(trigger_lit)] = (trigger_lit > 0)

    # --- UNIT PROPAGATION SİMÜLASYONU ---
    changed = True
    status = "CONTINUE"
    conflict_clause = "None"
    
    # Basit bir BCP döngüsü
    # (Not: Gerçek solver'da bu assignments solver state'inden gelmeli, 
    #  burada her stepte sıfırdan hesaplıyoruz ki bağımsız test edebilelim)
    
    while changed and status != "CONFLICT":
        changed = False
        for i, clause in enumerate(clauses):
            # Clause durumunu analiz et
            false_lits = 0
            unassigned_lits = []
            is_satisfied = False
            
            for lit in clause:
                var = abs(lit)
                # Mevcut turdaki atamalara bak
                if var in current_assignments:
                    val = current_assignments[var]
                    if (lit > 0 and val) or (lit < 0 and not val):
                        is_satisfied = True
                        break # Clause zaten sağlanmış, geç
                    else:
                        false_lits += 1 # Literal False olmuş
                else:
                    unassigned_lits.append(lit) # Henüz değeri yok
            
            if is_satisfied:
                continue
                
            # Durum 1: Conflict (Tüm literaller False oldu)
            if false_lits == len(clause):
                status = "CONFLICT"
                conflict_clause = f"Clause_{i+1}" # Örn: Clause_2
                break
            
            # Durum 2: Unit Clause (Sadece 1 tane atanmamış kalmış, kalanı False)
            if len(unassigned_lits) == 1 and false_lits == (len(clause) - 1):
                unit_lit = unassigned_lits[0]
                var = abs(unit_lit)
                val = (unit_lit > 0)
                
                # Eğer çelişkili bir atama yapmaya çalışıyorsak
                if var in current_assignments and current_assignments[var] != val:
                    status = "CONFLICT"
                    conflict_clause = f"Clause_{i+1}"
                    break
                
                # Yeni zorunlu atama (Implied)
                if var not in current_assignments:
                    current_assignments[var] = val
                    changed = True # Yeni atama yaptık, tekrar döngüye gir

    # Varsayım: Değişken sayısı, kullanılan clause'lardaki en büyük indeks
    max_var = 0
    for clause in clauses:
        for lit in clause:
            max_var = max(max_var, abs(lit))

    # Eğer conflict olmadıysa ve tüm clause'lar tatmin ediliyorsa, SAT olarak işaretle
    if status != "CONFLICT":
        all_sat = True
        for clause in clauses:
            clause_sat = False
            for lit in clause:
                var = abs(lit)
                val = current_assignments.get(var, None)
                if val is None:
                    continue
                if (lit > 0 and val) or (lit < 0 and not val):
                    clause_sat = True
                    break
            if not clause_sat:
                all_sat = False
                break
        if all_sat and max_var > 0:
            status = "SAT"
            conflict_clause = "None"
        else:
            status = "CONTINUE"

    # 3. Output Dosyasını Yaz (PDF'teki formata uygun)
    log_content = ""
    log_content += "--- STATUS ---\n"
    log_content += f"STATUS: {status}\n"
    log_content += f"DL: {dl}\n"
    log_content += f"CONFLICT_ID: {conflict_clause}\n\n"

    log_content += "--- BCP EXECUTION LOG ---\n"
    if trigger_lit != 0:
        log_content += f"[DL{dl}] DECIDE L={trigger_lit} |\n"
    else:
        log_content += f"[DL{dl}] INITIAL CHECK\n"
    log_content += f"[DL{dl}] PROPAGATION...\n\n"

    log_content += "--- CURRENT VARIABLE STATE ---\n"
    # Bulunan atamaları yaz (atanmamışlar UNASSIGNED)
    for var in range(1, max_var + 1):
        if var in current_assignments:
            v = current_assignments[var]
            state = "TRUE" if v else "FALSE"
        else:
            state = "UNASSIGNED"
        log_content += f"{var} | {state}\n"

    with open("bcp_output.txt", "w") as f:
        f.write(log_content)


# ==========================================
# BÖLÜM 2: DPLL SOLVER CLASS
# ==========================================
class DPLLSearchEngine:
    def __init__(self, cnf_clauses, num_vars, inference_cmd="inference_engine.exe"):
        self.clauses = cnf_clauses
        self.num_vars = num_vars
        self.assignments = {} 
        self.master_trace = [] 
        self.last_conflict_id = None
        self.inference_command = inference_cmd
        
        self.FILE_TRIGGER = "bcp_trigger_input.txt"
        self.FILE_BCP_OUT = "bcp_output.txt"
        self.FILE_MASTER_TRACE = "master_trace.txt"

    def get_unassigned_vars(self):
        all_vars = set(range(1, self.num_vars + 1))
        assigned_vars = set(self.assignments.keys())
        return list(all_vars - assigned_vars)

    def is_clause_satisfied(self, clause):
        for lit in clause:
            var = abs(lit)
            if var in self.assignments:
                val = self.assignments[var]
                if (lit > 0 and val) or (lit < 0 and not val):
                    return True
        return False

    def heuristic_jw(self, unassigned_vars):
        """Jeroslow-Wang Heuristic"""
        scores = {var: 0.0 for var in unassigned_vars}
        active_clauses = [c for c in self.clauses if not self.is_clause_satisfied(c)]
        
        if not active_clauses:
            return unassigned_vars[0] if unassigned_vars else None

        for clause in active_clauses:
            length = len(clause)
            weight = 2.0 ** (-length)
            for lit in clause:
                var = abs(lit)
                if var in scores:
                    scores[var] += weight
        
        return max(scores, key=scores.get)

    def write_trigger_input(self, literal, dl):
        """Trigger dosyasını oluşturur."""
        with open(self.FILE_TRIGGER, "w") as f:
            # PDF'e uygun başlık satırı
            f.write("# --- BCP TRIGGER INPUT ---\n")
            if literal == 0:
                f.write("TRIGGER_LITERAL: 0\n") 
            else:
                f.write(f"TRIGGER_LITERAL: {literal}\n")
            f.write(f"DL: {dl}\n")

    def read_bcp_output(self):
        """Output dosyasını okur ve parse eder."""
        if not os.path.exists(self.FILE_BCP_OUT):
            return {"status": "ERROR", "assignments": {}, "log": "File not found", "dl": None, "conflict_id": None}

        result = { "status": None, "assignments": {}, "log": "", "dl": None, "conflict_id": None }
        
        with open(self.FILE_BCP_OUT, "r") as f:
            lines = f.readlines()
            result["log"] = "".join(lines)

        section = None

        for raw_line in lines:
            line = raw_line.strip()
            if not line:
                continue

            # Bölüm başlıkları
            if line.startswith("--- STATUS ---"):
                section = "STATUS"
                continue
            elif line.startswith("--- BCP EXECUTION LOG ---"):
                section = "LOG"
                continue
            elif line.startswith("--- CURRENT VARIABLE STATE ---"):
                section = "VARS"
                continue

            if section == "STATUS":
                if line.startswith("STATUS:"):
                    result["status"] = line.split(":", 1)[1].strip()
                elif line.startswith("DL:"):
                    dl_str = line.split(":", 1)[1].strip()
                    try:
                        result["dl"] = int(dl_str)
                    except ValueError:
                        result["dl"] = None
                elif line.startswith("CONFLICT_ID:"):
                    result["conflict_id"] = line.split(":", 1)[1].strip()

            elif section == "VARS":
                # Biçim: "<var> | <STATE>"
                if "|" in line:
                    var_part, state_part = line.split("|", 1)
                    var_part = var_part.strip()
                    state_part = state_part.strip()
                    if var_part.isdigit():
                        var = int(var_part)
                        if state_part == "TRUE":
                            result["assignments"][var] = True
                        elif state_part == "FALSE":
                            result["assignments"][var] = False
                        # UNASSIGNED durumunda assignment ekleme
        return result

    def execute_inference_engine(self):
        # Normalde os.system çağırır. Mock ile override edilecek.
        os.system(self.inference_command)

    def solve(self):
        """Ana Çözümleme Fonksiyonu"""
        # ADIM 0: Initial Propagation (Karar vermeden önceki kontrol)
        print("DL: 0 Initial Propagation başlatılıyor...")
        self.write_trigger_input(literal=0, dl=0)
        self.execute_inference_engine()
        
        bcp_res = self.read_bcp_output()
        self.last_conflict_id = bcp_res.get("conflict_id")
        self.master_trace.append(bcp_res["log"])
        self.assignments.update(bcp_res["assignments"])

        status = bcp_res.get("status")

        # STATUS yorumlama
        if status in ("CONFLICT", "UNSAT"):
            return self.finalize("UNSAT")
        if status == "SAT":
            return self.finalize("SAT")
        
        if not self.get_unassigned_vars():
            return self.finalize("SAT")

        # Recursive aramayı başlat (DL 1'den)
        final_status = self.dpll_recursive(dl=0) 
        return self.finalize(final_status)

    def dpll_recursive(self, dl):
        unassigned = self.get_unassigned_vars()
        if not unassigned:
            return "SAT"

        # 1. Decision (Tahmin)
        var = self.heuristic_jw(unassigned)
        next_dl = dl + 1

        # --- BRANCH 1: TRUE ---
        saved_assignments = self.assignments.copy()
        
        self.write_trigger_input(var, next_dl)
        self.execute_inference_engine()
        
        bcp_res = self.read_bcp_output()
        self.last_conflict_id = bcp_res.get("conflict_id")
        self.master_trace.append(bcp_res["log"])
        
        status = bcp_res["status"]
        
        if status == "SAT":
            self.assignments.update(bcp_res["assignments"])
            return "SAT"
        
        if status not in ("CONFLICT", "UNSAT"):
            self.assignments.update(bcp_res["assignments"])
            self.assignments[var] = True
            
            if self.dpll_recursive(next_dl) == "SAT":
                return "SAT"
        
        # --- BRANCH 2: FALSE (Backtracking) ---
        self.assignments = saved_assignments # State'i geri al
        
        # Trigger: Negatifini dene
        self.write_trigger_input(-var, next_dl)
        self.execute_inference_engine()
        
        bcp_res = self.read_bcp_output()
        self.last_conflict_id = bcp_res.get("conflict_id")
        self.master_trace.append(bcp_res["log"])
        
        status = bcp_res["status"]
        
        if status == "SAT":
            self.assignments.update(bcp_res["assignments"])
            return "SAT"
        
        if status not in ("CONFLICT", "UNSAT"):
            self.assignments.update(bcp_res["assignments"])
            self.assignments[var] = False
            
            if self.dpll_recursive(next_dl) == "SAT":
                return "SAT"

        # İki branch de başarısız
        self.assignments = saved_assignments
        return "UNSAT"

    def finalize(self, status):
        print(f"Final Status: {status}")
        with open(self.FILE_MASTER_TRACE, "w") as f:
            # Trace loglarını ayraç ile birleştir
            f.write("\n-------------------------------------------------\n".join(self.master_trace))
        result = {
            "status": status,
            "model": self.assignments.copy() if status == "SAT" else None,
            "trace_file": self.FILE_MASTER_TRACE,
            "final_conflict_id": self.last_conflict_id,
        }
        return result


if __name__ == "__main__":
    # This block runs ONLY if you execute 'python main.py' directly.
    # It demonstrates the solver using the example from the Project PDF.
    
    print("--- BLG 345E Project #4: DPLL Search Engine Demo ---")
    
    # PDF Sample: (-A v B) ^ (-B v -C) ^ (C v A) ^ (-B v C)
    # Mapping: A=1, B=2, C=3
    clauses = [[-1, 2], [-2, -3], [3, 1], [-2, 3]]
    vars = 3
    
    # Initialize Solver
    # Defaulting to "mock" mode for safe demonstration
    solver = DPLLSearchEngine(clauses, vars, inference_cmd="mock")
    solver.execute_inference_engine = mock_inference_engine_generic
    
    # Clean previous run files
    if os.path.exists("bcp_output.txt"): os.remove("bcp_output.txt")
    if os.path.exists("master_trace.txt"): os.remove("master_trace.txt")

    print(f"Solving PDF Sample Formula: {clauses}")
    result = solver.solve()
    
    print(f"\nFINAL STATUS: {result['status']}")
    print(f"ASSIGNMENTS:  {result['model']}")
    print(f"FINAL CONFLICT ID: {result['final_conflict_id']}")
    print("\n(Full execution log saved to 'master_trace.txt')")