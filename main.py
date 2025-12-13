import os
import math

class DPLLSearchEngine:
    def __init__(self, cnf_clauses, num_vars):
        """
        DPLL Motorunu başlatır.
        cnf_clauses: List of lists (her iç liste bir clause, örn: [1, -2, 3])
        num_vars: Toplam değişken sayısı.
        """
        self.clauses = cnf_clauses
        self.num_vars = num_vars
        self.assignments = {}  # Değişken atamaları: {var_id: True/False}
        self.master_trace = [] # Master Trace for Project #5 
        
    def get_unassigned_vars(self):
        """Henüz atanmamış değişkenleri döndürür."""
        all_vars = set(range(1, self.num_vars + 1))
        assigned_vars = set(self.assignments.keys())
        return list(all_vars - assigned_vars)

    def heuristic_jw(self, unassigned_vars):
        """
        Gereksinim 1.1.2: Decision Heuristics.
        Jeroslow-Wang (Two-sided) algoritması.
        J(l) = sum(2^(-|C|)) for clauses C containing l.
        """
        scores = {}
        
        # Sadece tatmin edilmemiş clause'lara bakmalıyız
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

        # Ağırlıkları hesapla
        for var in unassigned_vars:
            score = 0
            # Literal pozitif ve negatif ağırlıkları
            pos_score = 0
            neg_score = 0
            
            for clause in active_clauses:
                length = len(clause)
                weight = 2 ** (-length)
                if var in clause:
                    pos_score += weight
                if -var in clause:
                    neg_score += weight
            
            # Two-sided JW: Genellikle pos_score + neg_score veya max alınır.
            # Burada toplamı alarak en etkili değişkeni seçiyoruz.
            scores[var] = pos_score + neg_score

        # Skoru en yüksek olan değişkeni döndür
        if not scores:
            return unassigned_vars[0] # Fallback
            
        best_var = max(scores, key=scores.get)
        
        # Karar değeri seçimi (True mu False mu denenecek?)
        # Pozitif literal skoru daha yüksekse True, değilse False denebilir.
        # Bu örnekte varsayılan olarak True deniyoruz, ama trace için önemli.
        return best_var

    def write_trigger_input(self, literal, dl):
        """
        Gereksinim 1.2.1: BCP Trigger Input dosyası oluşturur[cite: 48, 52].
        """
        content = "#\nBCP TRIGGER INPUT\n"
        content += f"TRIGGER LITERAL: {literal}\n"
        content += f"DL: {dl}\n"
        
        with open("bcp_trigger_input.txt", "w") as f:
            f.write(content)

    def read_bcp_output(self):
        """
        Gereksinim 1.2.2: BCP Output dosyasını okur ve durumu analiz eder[cite: 54].
        Döndürdüğü: STATUS, CONFLICT_ID, LOG
        """
        # Not: Gerçek senaryoda Inference Engine'in çalışmasını beklemelisiniz.
        # Burada dosyanın var olduğunu ve güncellendiğini varsayıyoruz.
        
        result = {
            "status": None,
            "dl": 0,
            "conflict_id": None,
            "log": "",
            "assignments": {}
        }
        
        if not os.path.exists("bcp_output.txt"):
            raise FileNotFoundError("BCP Output dosyası bulunamadı!")

        with open("bcp_output.txt", "r") as f:
            lines = f.readlines()
            
        # Basit parsing mantığı (Proje gereksinimlerine göre detaylandırılmalı)
        reading_state = "HEADER"
        for line in lines:
            line = line.strip()
            if line.startswith("STATUS:"):
                result["status"] = line.split(":")[1].strip()
            elif line.startswith("CONFLICT_ID:"):
                val = line.split(":")[1].strip()
                result["conflict_id"] = int(val) if val != "None" else None
            elif line == "BCP EXECUTION LOG":
                reading_state = "LOG"
            elif line == "CURRENT VARIABLE STATE":
                reading_state = "VARS"
            
            if reading_state == "LOG" and line != "BCP EXECUTION LOG":
                result["log"] += line + "\n"
                
            # Variable state parsing kısmını burada detaylandırabilirsin [cite: 78]
            # Örn: 1\n | UNASSIGNED okuma mantığı.

        return result

    def dpll_recursive(self, dl):
        """
        Gereksinim 1.1.1: Rekürsif DPLL Fonksiyonu[cite: 21].
        """
        # 1. Unassigned değişkenleri bul
        unassigned = self.get_unassigned_vars()
        
        # Eğer tüm değişkenler atanmışsa ve CONFLICT yoksa SAT bulundu demektir.
        if not unassigned:
            return "SAT"

        # 2. Heuristic ile değişken seç (Decision) [cite: 26, 30]
        var = self.heuristic_jw(unassigned)
        
        # Branch 1: Değişkeni TRUE olarak dene (Literal = var)
        # Karar seviyesini artır [cite: 37]
        target_dl = dl + 1
        
        # Inference Engine'i tetikle [cite: 22]
        self.write_trigger_input(var, target_dl)
        
        # --- BURADA INFERENCE ENGINE (PROJE #3) ÇALIŞMALI ---
        # os.system("./inference_engine") # Bu satır entegrasyonda açılmalı
        
        # Sonucu oku [cite: 23]
        bcp_result = self.read_bcp_output()
        self.master_trace.append(bcp_result["log"]) # Trace kaydı [cite: 86]

        if bcp_result["status"] == "SAT":
            return "SAT" # [cite: 24]
        
        elif bcp_result["status"] == "CONFLICT":
            # Backtrack işlemi Inference Engine tarafından state temizlenerek yapılır,
            # ancak biz burada 'karşıt dalı' denemeliyiz.
            # Şu anki dal başarısız oldu.
            pass # Branch 2'ye geç [cite: 25, 28]
            
        else: # CONTINUE
            # Rekürsif çağrı [cite: 27]
            self.assignments[var] = True # Geçici kabul (Inference engine güncelledi varsayıyoruz)
            if self.dpll_recursive(target_dl) == "SAT":
                return "SAT"
            
            # Eğer yukarıdaki return olmadıysa, recursive call fail etti demektir.
            # Backtrack: Atamayı geri al 
            del self.assignments[var]

        # Branch 2: Değişkeni FALSE olarak dene (Literal = -var)
        # Önceki deneme başarısız olduysa buraya geliriz.
        
        self.write_trigger_input(-var, target_dl)
        
        # --- INFERENCE ENGINE ÇAĞRISI ---
        # os.system("./inference_engine")
        
        bcp_result = self.read_bcp_output()
        self.master_trace.append(bcp_result["log"])

        if bcp_result["status"] == "SAT":
            return "SAT"
        elif bcp_result["status"] == "CONFLICT":
            return "UNSAT" # Her iki dal da (True/False) başarısız [cite: 25]
        else: # CONTINUE
            self.assignments[var] = False
            if self.dpll_recursive(target_dl) == "SAT":
                return "SAT"
            del self.assignments[var]
            return "UNSAT"

    def solve(self):
        """Çözümü başlatan ana fonksiyon"""
        # Initial check (DL 0) [cite: 102]
        # DL 0 için Inference Engine çağrısı yapılabilir (Unit propagation kontrolü)
        
        status = self.dpll_recursive(0)
        
        # Çıktı oluşturma [cite: 43]
        final_output = f"STATUS: {status}\n"
        if status == "SAT":
             final_output += str(self.assignments)
        
        # Master Trace dosyasını yaz 
        with open("master_trace.txt", "w") as f:
            f.write("".join(self.master_trace))
            
        return status



clauses = [[-1, 2], [-2, -3], [3, 1], [-2, 3]] # Örnek formül [cite: 98]
solver = DPLLSearchEngine(clauses, 3)
result = solver.solve()
print(result)