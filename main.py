import os
import sys

class DPLLSearchEngine:
    def __init__(self, cnf_clauses, num_vars):
        self.clauses = cnf_clauses
        self.num_vars = num_vars
        self.assignments = {}  
        self.master_trace = [] 
        
        # Kullanılacak Inference Engine'in komutu.
        # Eğer C++ exe ise: "inference_engine.exe" veya "./inference_engine"
        # Eğer Python ise: "python inference_engine.py"
        self.inference_command = "inference_engine.exe" 

    def get_unassigned_vars(self):
        """Dinamik olarak atanmamış değişkenleri bulur."""
        all_vars = set(range(1, self.num_vars + 1))
        assigned_vars = set(self.assignments.keys())
        return list(all_vars - assigned_vars)

    def heuristic_jw(self, unassigned_vars):
        """
        Jeroslow-Wang Heuristic.
        Gelen formül ne olursa olsun, en kritik değişkeni matematiksel olarak seçer.
        """
        scores = {}
        
        # Mevcut atamalara göre clause'ların durumunu analiz et
        active_clauses = []
        for clause in self.clauses:
            is_satisfied = False
            for lit in clause:
                var = abs(lit)
                val = self.assignments.get(var)
                if (lit > 0 and val is True) or (lit < 0 and val is False):
                    is_satisfied = True
                    break
            if not is_satisfied:
                active_clauses.append(clause)

        # Hiç active clause kalmadıysa (hepsi satisfied) ama unassigned varsa, rastgele seç
        if not active_clauses:
             return unassigned_vars[0]

        # Puanlama
        for var in unassigned_vars:
            score = 0
            for clause in active_clauses:
                if var in clause or -var in clause:
                    length = len(clause)
                    weight = 2.0 ** (-length)
                    score += weight
            scores[var] = score

        if not scores:
            return unassigned_vars[0]
            
        # En yüksek puanlıyı döndür
        return max(scores, key=scores.get)

    def write_trigger_input(self, literal, dl):
        """
        Herhangi bir değişken ve DL için trigger dosyası oluşturur.
        """
        content = "#\nBCP TRIGGER INPUT\n"
        content += f"TRIGGER LITERAL: {literal}\n"
        content += f"DL: {dl}\n"
        
        with open("bcp_trigger_input.txt", "w") as f:
            f.write(content)

    def read_bcp_output(self):
        """
        Inference Engine'in ürettiği çıktıyı GENEL olarak okur.
        Değişken sayısı veya isimleri ne olursa olsun çalışır.
        """
        if not os.path.exists("bcp_output.txt"):
             # Hata yönetimi: Eğer dosya yoksa motor çalışmamış demektir.
             # Debug için print ekleyebilirsin.
             raise FileNotFoundError("BCP Output dosyası bulunamadı! Inference Engine çalıştırılamadı.")

        result = {
            "status": None,
            "log": "",
            "assignments_from_bcp": {} 
        }

        with open("bcp_output.txt", "r") as f:
            lines = f.readlines()
            
        reading_state = "HEADER"
        current_var_processing = None

        for line in lines:
            line = line.strip()
            
            # Header
            if line.startswith("STATUS:"):
                result["status"] = line.split(":")[1].strip()
            elif line == "BCP EXECUTION LOG":
                reading_state = "LOG"
            elif line == "CURRENT VARIABLE STATE":
                reading_state = "VARS"
                continue
            
            # Log Toplama
            if reading_state == "LOG" and line != "BCP EXECUTION LOG" and line != "CURRENT VARIABLE STATE":
                result["log"] += line + "\n"
                
            # Dinamik Variable State Okuma
            if reading_state == "VARS":
                if not line or line.startswith("#"): continue
                
                # Format: "VariableID" alt satırda "| STATE"
                if line.isdigit():
                    current_var_processing = int(line)
                elif line.startswith("|") and current_var_processing is not None:
                    state_val = line.split("|")[1].strip()
                    if state_val == "TRUE":
                        result["assignments_from_bcp"][current_var_processing] = True
                    elif state_val == "FALSE":
                        result["assignments_from_bcp"][current_var_processing] = False
                    current_var_processing = None

        return result

    def sync_assignments(self, bcp_assignments):
        """Search Engine hafızasını günceller."""
        # Inference Engine "Bu değişkenler zorunlu" dediyse onları kabul et.
        self.assignments.update(bcp_assignments)

    def dpll_recursive(self, dl):
        """
        Evrensel DPLL Döngüsü
        """
        # 1. Atanacak değişken kaldı mı?
        unassigned = self.get_unassigned_vars()
        if not unassigned:
            return "SAT"

        # 2. Heuristic ile en iyi değişkeni seç
        var = self.heuristic_jw(unassigned)
        
        # --- BRANCH 1: TRUE DENE ---
        target_dl = dl + 1
        
        # a) Dosyayı yaz
        self.write_trigger_input(var, target_dl)
        
        # b) GERÇEK MOTORU ÇAĞIR (Burada sihir gerçekleşiyor)
        # Windows kullanıyorsan ve exe ise sadece ismini, python ise 'python script.py'
        exit_code = os.system(self.inference_command)
        if exit_code != 0:
             print("HATA: Inference Engine düzgün çalışmadı!")
        
        # c) Sonucu oku
        bcp_result = self.read_bcp_output()
        self.master_trace.append(bcp_result["log"]) 
        
        status = bcp_result["status"]
        
        # Bu aşamada yapılan atamaları geçici olarak kaydetmek için kopyala
        saved_assignments = self.assignments.copy()

        if status == "SAT":
            self.sync_assignments(bcp_result["assignments_from_bcp"])
            return "SAT"
        
        elif status == "CONFLICT":
            pass # Backtrack (Aşağıdaki False branch'ine git)

        else: # CONTINUE
            self.sync_assignments(bcp_result["assignments_from_bcp"])
            # Kendi kararımızı da ekle (Inference Engine bazen sadece propagate ettiklerini dönebilir)
            self.assignments[var] = True 
            
            if self.dpll_recursive(target_dl) == "SAT":
                return "SAT"
            
            # Backtrack: Fail ettiyse state'i geri yükle
            self.assignments = saved_assignments

        # --- BRANCH 2: FALSE DENE ---
        self.write_trigger_input(-var, target_dl)
        
        # GERÇEK MOTORU ÇAĞIR
        os.system(self.inference_command)
        
        bcp_result = self.read_bcp_output()
        self.master_trace.append(bcp_result["log"])
        
        status = bcp_result["status"]
        
        saved_assignments_branch2 = self.assignments.copy() # Mevcut state (Branch 1'den temizlenmiş hali)

        if status == "SAT":
            self.sync_assignments(bcp_result["assignments_from_bcp"])
            return "SAT"
        elif status == "CONFLICT":
            return "UNSAT" # İki yol da kapalı
        else: # CONTINUE
            self.sync_assignments(bcp_result["assignments_from_bcp"])
            self.assignments[var] = False
            
            if self.dpll_recursive(target_dl) == "SAT":
                return "SAT"
            
            self.assignments = saved_assignments_branch2
            return "UNSAT"

    def solve(self):
        """
        Çözümü başlatır.
        """
        # Adım 1: Initial State (DL 0) kontrolü.
        # Bu çok önemli çünkü input ne olursa olsun, başta unit clause varsa
        # Inference Engine (Proje 2'den çıktıktan sonra) bunları bcp_output.txt'ye yazmış olmalı.
        # Biz de oradan okuyup başlarız.
        
        if os.path.exists("bcp_output.txt"):
             initial_bcp = self.read_bcp_output()
             self.master_trace.append(initial_bcp["log"])
             self.sync_assignments(initial_bcp["assignments_from_bcp"])
             
             if initial_bcp["status"] == "SAT":
                 return self.finalize("SAT")
             if initial_bcp["status"] == "CONFLICT":
                 return self.finalize("UNSAT")
        else:
             # Dosya yoksa, Inference Engine'i boş bir trigger ile DL 0 için dürtmemiz gerekebilir
             # veya Proje 3 tasarımına göre o zaten başta çalışmıştır.
             pass 

        # Adım 2: Recursive DPLL
        status = self.dpll_recursive(0)
        return self.finalize(status)

    def finalize(self, status):
        """Sonuçları dosyaya yazar ve döner"""
        with open("master_trace.txt", "w") as f:
            f.write("".join(self.master_trace))
        return status

# --- MAIN ---
if __name__ == "__main__":
    # Bu kısmı kendi proje yapına göre doldurmalısın.
    # clauses ve num_vars değerlerini Proje 2'nin çıktısından (parsed cnf) okumalısın.
    # Şimdilik örnek veriyorum:
    
    # ÖRNEK: Input ne gelirse gelsin buraya o parametreleri vermelisin.
    clauses = [[-1, 2], [-2, -3], [3, 1], [-2, 3]] 
    num_vars = 3
    
    solver = DPLLSearchEngine(clauses, num_vars)
    
    # ÖNEMLİ: Inference Engine dosya yolunu ayarla
    # Aynı klasörde 'inference_engine.exe' varsa:
    solver.inference_command = "inference_engine.exe" 
    
    print("Çözüm Başlıyor...")
    result = solver.solve()
    print(f"SONUÇ: {result}")
    print(f"ATAMALAR: {solver.assignments}")