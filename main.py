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
                if "TRIGGER LITERAL" in line:
                    val = line.split(":")[1].strip()
                    trigger_lit = int(val) if val else 0
                if "DL" in line:
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

    # 3. Output Dosyasını Yaz
    log_content = f"STATUS: {status}\nDL: {dl}\nCONFLICT_ID: {conflict_clause}\nBCP EXECUTION LOG\n"
    
    if trigger_lit != 0:
        log_content += f"[DL{dl}] DECIDE $L={trigger_lit}$\n"
    else:
        log_content += f"[DL{dl}] INITIAL CHECK\n"
        
    log_content += f"[DL{dl}] PROPAGATION...\nCURRENT VARIABLE STATE\n"
    
    # Bulunan atamaları yaz
    for k, v in current_assignments.items():
        log_content += f"{k}\n| {'TRUE' if v else 'FALSE'}\n"

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
            f.write("#\nBCP TRIGGER INPUT\n")
            if literal == 0:
                f.write("TRIGGER LITERAL: 0\n") 
            else:
                f.write(f"TRIGGER LITERAL: {literal}\n")
            f.write(f"DL: {dl}\n")

    def read_bcp_output(self):
        """Output dosyasını okur ve parse eder."""
        if not os.path.exists(self.FILE_BCP_OUT):
            return {"status": "ERROR", "log": "File not found"}

        result = { "status": None, "assignments": {}, "log": "" }
        
        with open(self.FILE_BCP_OUT, "r") as f:
            lines = f.readlines()
            result["log"] = "".join(lines)

        section = "HEADER"
        current_var = None

        for line in lines:
            line = line.strip()
            if not line: continue

            if line.startswith("STATUS:"):
                result["status"] = line.split(":")[1].strip()
            
            elif line == "CURRENT VARIABLE STATE":
                section = "VARS"
                continue

            if section == "VARS":
                if line.isdigit():
                    current_var = int(line)
                elif line.startswith("|") and current_var is not None:
                    val_str = line.split("|")[1].strip()
                    if val_str == "TRUE":
                        result["assignments"][current_var] = True
                    elif val_str == "FALSE":
                        result["assignments"][current_var] = False
                    current_var = None
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
        self.master_trace.append(bcp_res["log"])
        self.assignments.update(bcp_res["assignments"])

        if bcp_res["status"] == "CONFLICT":
            return self.finalize("UNSAT")
        
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
        self.master_trace.append(bcp_res["log"])
        
        status = bcp_res["status"]
        
        if status != "CONFLICT":
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
        self.master_trace.append(bcp_res["log"])
        
        status = bcp_res["status"]
        
        if status != "CONFLICT":
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
        return status

# ==========================================
# BÖLÜM 3: MAIN TEST BLOĞU
# ==========================================
if __name__ == "__main__":
    
    # --- BURAYI DEĞİŞTİREREK TEST ET ---
    # 1: UNSAT (Çelişkili)
    # 2: DOMINO (Sadece Unit Propagation)
    # 3: DEEP SEARCH (Branching gerektiren)
    TEST_SCENARIO = 3
    # -----------------------------------

    if TEST_SCENARIO == 1:
        print("\n=== TEST 1: UNSAT (Çelişki) ===")
        clauses = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
        num_vars = 2

    elif TEST_SCENARIO == 2:
        print("\n=== TEST 2: DOMİNO ETKİSİ ===")
        clauses = [[1], [-1, 2], [-2, 3]]
        num_vars = 3

    elif TEST_SCENARIO == 3:
        print("\n=== TEST 3: DERİN ARAMA (Branching) ===")
        # 1. Karar yetmeyecek, geri dönecek veya derine inecek
        clauses = [[1, 2], [-1, 3], [-3, 4], [-2, -4]]
        num_vars = 4
    
    # Temizlik
    if os.path.exists("bcp_output.txt"): os.remove("bcp_output.txt")
    if os.path.exists("master_trace.txt"): os.remove("master_trace.txt")

    # Solver Kurulumu
    solver = DPLLSearchEngine(clauses, num_vars, inference_cmd="mock")
    # Mock motoru bağla
    solver.execute_inference_engine = mock_inference_engine_generic 
    
    print("--- Search Engine Başlatılıyor ---")
    result = solver.solve()
    
    print(f"\n--- SONUÇ: {result} ---")
    print("Final Atamalar:", solver.assignments)
    
    print("\n--- MASTER TRACE DOSYASI İÇERİĞİ ---")
    if os.path.exists("master_trace.txt"):
        with open("master_trace.txt", "r") as f:
            print(f.read())