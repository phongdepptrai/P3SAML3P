# P3SAML3P — SAT-based Assembly Line Balancing Solver

Dự án giải bài toán **cân bằng dây chuyền lắp ráp (Assembly Line Balancing)** với ràng buộc tài nguyên, sử dụng nhiều chiến lược encode SAT/MaxSAT khác nhau. Mỗi phiên bản solver thử nghiệm một cách tiếp cận encode khác nhau để tối thiểu hoá **đỉnh tải (peak load)**.

---

## Mục lục

- [Bài toán](#bài-toán)
- [Cài đặt \& Chạy](#cài-đặt--chạy)
- [Tóm tắt các phiên bản Solver](#tóm-tắt-các-phiên-bản-solver)
- [Mô tả các Constraint](#mô-tả-các-constraint)
- [Cấu trúc thư mục](#cấu-trúc-thư-mục)
- [Định dạng Output](#định-dạng-output)
- [Bộ dữ liệu](#bộ-dữ-liệu)

---

## Bài toán

Cho một đồ thị ưu tiên (precedence graph) gồm `n` task với thời gian thực hiện `t_j`, cần phân công mỗi task lên một trong `m` máy và xác định thời điểm bắt đầu `S[j]`, sao cho:

- Ràng buộc ưu tiên `i ≺ j` được thoả mãn (task i hoàn thành trước task j bắt đầu nếu cùng máy).
- Không có hai task chồng lấn nhau trên cùng máy.
- Tổng số resource được phân bổ không vượt quá ngân sách `R_max`.
- **Tối thiểu hoá đỉnh tải** (peak load): giá trị lớn nhất của tổng `W[j]` trên mọi task j đang chạy tại cùng một pha thời gian.

**Thông số:**

| Ký hiệu | Ý nghĩa |
|---|---|
| `n` | Số task |
| `m` | Số máy (stations) |
| `c` | Chu kỳ (cycle time) |
| `r_max` | Số resource tối đa mỗi máy |
| `R_max` | Tổng resource toàn tuyến |
| `W[j]` | Trọng số tải của task j |
| `horizon` | Cửa sổ thời gian = `c × r_max` |

---

## Cài đặt & Chạy

### 1. Tạo môi trường ảo

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install python-sat tabulate pandas openpyxl pypblib
```

### 2. Chạy qua launcher (menu chọn solver)

```bash
source .venv/bin/activate
python run_launcher.py
```

### 3. Chạy trực tiếp một solver

```bash
# Chạy toàn bộ bộ test (batch)
python solvers/<SolverName>.py

# Chạy một instance cụ thể: <instance_id> <r_max> <R_max>
python solvers/<SolverName>.py 0 1 6
```

### 4. Chạy qua runner script (có hỗ trợ runlim)

```bash
python runners/<SolverName>_run.py
```

---

## Tóm tắt các phiên bản Solver

| Phiên bản | File | Chiến lược No-Overlap (C6) | Encode X/S | Intermediate log | Ghi chú |
|---|---|---|---|---|---|
| **base** | `solvers/base.py` | 4-literal A vars: `[-X[i][k],-X[j][k],-A[i][t],-A[j][t]]` | Staircase Y + Staircase T | ✅ | Phiên bản nền tảng, encode đơn giản nhất |
| **Atmostk** | `solvers/Atmostk.py` | 4-literal A vars (giống base) | Staircase Y + Staircase T | ✅ | Thêm AtMostK encoding cho resource |
| **Staircase13** | `solvers/Staircase13.py` | 4-literal A vars | Staircase Y + Staircase T | ✅ | Variant staircase, tên theo encoding |
| **Incremental** | `solvers/Incremental.py` | 4-literal A vars + C8 bằng T vars | Staircase Y + Staircase T | ✅ | Thêm C8 tighten theo thời gian dùng T (prefix sum) |
| **Inheritant** | `solvers/Inheritant.py` | 4-literal A vars + C8 bằng T vars | Staircase Y + Staircase T | ✅ | Tương tự Incremental, thêm ràng buộc kế thừa precedence |
| **IncrementalSM** | `solvers/IncrementalSM.py` | **SM encoding** — biến phụ `SM[i][j]`, dùng T vars thay A vars | Staircase Y + Staircase T | ✅ | **Mới nhất** — loại bỏ A vars khỏi no-overlap |
| **maxsat** | `solvers/maxsat.py` | 4-literal A vars | Staircase Y + Staircase T | ❌ | Dùng RC2 MaxSAT, không có intermediate |

### So sánh C6 No-Overlap — Số mệnh đề

| Phiên bản | Constraint | Độ phức tạp | Loại literal |
|---|---|---|---|
| base / Atmostk / Staircase / Incremental / Inheritant / maxsat | `[-X[i][k], -X[j][k], -A[i][t], -A[j][t]]` | O(n² × m × horizon) | 4-literal |
| **IncrementalSM — C6a** | `[-X[i][k], -X[j][k], SM[i][j]]` | O(n² × m) | 3-literal |
| **IncrementalSM — C6b** | `[-X[i][k], -X[j][l], -SM[i][j]]` (k≠l) | O(n² × m²) | 3-literal |
| **IncrementalSM — C6c** | `[-SM[i][j], -S[i][t], ±T[j][...]]` (2 chiều) | O(n² × horizon) | 3-literal |

### Chiến lược tối ưu hoá

| Phiên bản | Chiến lược |
|---|---|
| base / Atmostk / Staircase / Incremental / Inheritant / IncrementalSM | Vòng lặp tuyến tính: thắt chặt dần bound, dùng INAGURAL ladder vars `U[i]` |
| **maxsat** | Một lần gọi RC2 MaxSAT (pysat) — tối ưu trực tiếp, không có intermediate |

---

## Mô tả các Constraint

| Tên | Nội dung |
|---|---|
| **C1+C2** | Staircase encoding cho X (ALO+AMO): mỗi task được gán đúng 1 máy, dùng biến phụ `Y[j][k]` |
| **C3+C4** | Staircase encoding cho S (ALO+AMO): mỗi task có đúng 1 thời điểm bắt đầu, dùng biến phụ `T[j][t]` |
| **C5** | Liên tục: `S[j][t] → A[j][t..t+tj-1]` — task chạy liên tục từ khi bắt đầu |
| **C6** | No-overlap (các solver cũ): hai task cùng máy không chạy đồng thời, dùng A vars |
| **C6a** | SM indicator định nghĩa: `(X[i][k] ∧ X[j][k]) → SM[i][j]` |
| **C6b** | SM indicator phủ định: `(X[i][k] ∧ X[j][l]) → ¬SM[i][j]` với k≠l |
| **C6c** | No-overlap dùng SM+T: `SM[i][j] ∧ S[i][t] → T[j][t-tj] ∨ ¬T[j][t+ti-1]` (2 chiều) |
| **C7** | Precedence → thứ tự máy: `Y[j][k] → ¬X[i][k+1]` (nếu i≺j thì j không ở trạm sớm hơn i) |
| **C8** | Precedence → thứ tự thời gian: nếu i≺j cùng máy, i phải kết thúc trước j bắt đầu (dùng T vars) |
| **C9** | Đơn điệu resource: `R[k][r+1] → R[k][r]` |
| **C10** | Liên hệ start-time với resource: `S[j][t] ∧ X[j][k] → R[k][q-1]` với q=⌈(t+tj)/c⌉ |
| **C11** | Ngân sách resource toàn tuyến: `Σ R[k][r] ≤ R_max` (PBEnc BinMerge) |
| **INAGURAL** | Ladder vars `U[i]` cho từng pha thời gian, dùng để tighten peak bound ở mỗi vòng lặp |

---

## Cấu trúc thư mục

```
P3SAML3P/
├── README.md
├── run_launcher.py          # Menu chọn và chạy solver
├── generate_table.py        # Sinh bảng kết quả tổng hợp
├── validate_schedule.py     # Kiểm tra tính đúng đắn của lịch trình
├── runlim                   # Binary giám sát tài nguyên (Linux x86-64)
│
├── solvers/                 # Các phiên bản solver
│   ├── base.py
│   ├── Atmostk.py
│   ├── Staircase13.py
│   ├── Incremental.py
│   ├── Inheritant.py
│   ├── IncrementalSM.py     # SM encoding — phiên bản mới nhất
│   └── maxsat.py
│
├── runners/                 # Wrapper scripts (runlim + Linux/WSL dual support)
│   ├── base_run.py
│   ├── Atmostk_run.py
│   ├── Staircase_run.py
│   ├── Incremental_run.py
│   ├── Inheritant_run.py
│   ├── IncrementalSM_run.py
│   └── maxsat_run.py
│
├── presedent_graph/         # File input đồ thị ưu tiên (.IN2)
├── official_task_power/     # File trọng số task (.txt)
└── Output/                  # Kết quả chạy (tự sinh)
    └── <SolverName>/
        ├── summary.csv
        ├── summary.xlsx
        └── <instance>_n<n>_m<m>_c<c>/
            └── r<r>_R<R>/
                └── <instance>_..._r<r>_R<R>.html
```

---

## Định dạng Output

### `summary.csv` / `summary.xlsx`

| Cột | Ý nghĩa |
|---|---|
| `name` | Tên instance |
| `n` / `m` / `c` | Số task / máy / chu kỳ |
| `r_max` / `R_max` | Tham số resource |
| `base_vars` | Số biến SAT cơ sở |
| `base_clauses` | Số mệnh đề SAT cơ sở |
| `peak` | Đỉnh tải tốt nhất tìm được |
| `attempts` | Số vòng lặp tối ưu |
| `runtime_sec` | Thời gian chạy (giây) |
| `status` | `STARTED` / `FEASIBLE` / `INTERMEDIATE` / `OPTIMAL` / `TIMEOUT_INFEASIBLE` |

---

## Bộ dữ liệu

Các instance từ bộ chuẩn SALBP, chạy với `r_max ∈ {1,2,3}` và `R_max ∈ [m, r_max × m]`:

| ID | Tên | m | c | Độ khó |
|---|---|---|---|---|
| 0 | MERTENS | 6 | 6 | Easy |
| 1 | MERTENS | 2 | 18 | Easy |
| 2 | BOWMAN | 5 | 20 | Easy |
| 3 | JAESCHKE | 8 | 6 | Easy |
| 4 | JAESCHKE | 3 | 18 | Easy |
| 5 | JACKSON | 8 | 7 | Easy |
| 6 | JACKSON | 3 | 21 | Easy |
| 7 | MANSOOR | 4 | 48 | Easy |
| 8 | MANSOOR | 2 | 94 | Easy |
| 9 | MITCHELL | 8 | 14 | Easy |
| 10 | MITCHELL | 3 | 39 | Easy |
| 11 | ROSZIEG | 10 | 14 | Easy |
| 12 | ROSZIEG | 4 | 32 | Easy |
| 13 | BUXEY | 14 | 25 | Hard |
| 14 | BUXEY | 7 | 47 | Hard |
| 15 | SAWYER | 14 | 25 | Hard |
| 16 | SAWYER | 7 | 47 | Hard |

---

## Dependencies

```
python-sat   # SAT solver (CaDiCaL195, RC2, PBEnc)
tabulate     # Định dạng bảng terminal
pandas       # Xuất Excel
openpyxl     # Engine ghi .xlsx
pypblib      # Pseudo-Boolean encoding (PBEnc)
```
