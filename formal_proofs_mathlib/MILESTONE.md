Chốt ngay bản kế hoạch **Milestone 9A2 (`formal_proofs_mathlib/CriticalProdiSerrinTorus3D.lean`)** để Nam lưu vào tài liệu milestone và bàn sâu đêm nay — giữ trọn sự mạch lạc, không vòng tròn, `0 sorryAx`, và bám đúng trục *"hạ cấp ngòi nổ $Z^3 \to Z$ + không rời mắt khỏi chiếc lá trên dòng thời gian"*.

---

### Kế Hoạch Triển Khai Milestone 9A2 (`CriticalProdiSerrinTorus3D.lean`)

**Vị trí trong kiến trúc hiện tại:**

* Đứng trên nhánh `research/m9-supercritical-barrier` (đã lưu gọn `EnstrophyBasinTorus3D.lean` — 8/8 định lý Tầng I vô điều kiện, `0 sorryAx`).
* Kế thừa trực tiếp `EnstrophyBasinTorus3D` (đặc biệt bất đẳng thức vô điều kiện $\frac{dZ}{dt} \le -\frac{\nu}{4} P + c_\nu Z^3$ với $c_\nu := \frac{169}{8\pi^4\nu^3}$, ngưỡng bồn $Z_{\mathrm{crit}}(\nu) = \frac{4\pi^3}{13}\nu^2$, và mốc bẫy $T_{\mathrm{trap}} = \frac{13 E_0}{4\pi^3\nu^3}$).
* Mục tiêu của 9A2: **hạ cấp bất đẳng thức bậc 3 ($Z^3$) thành phương trình tuyến tính theo $Z$ với hệ số phụ thuộc chuẩn tới hạn Prodi–Serrin $L^4_t \dot{H}^1_x$**, đồng thời khóa **bước nhảy an toàn từng nhịp thời gian** trước khi nối sang Garry (Rust) ở 9B.

---

### Bốn Mũi Định Lý Cốt Lõi Của Milestone 9A2 (Tầng I — Vô Điều Kiện, `0 sorryAx`)

1. **Định lý 9A2-1 — Hạ Cấp $Z^3 \to \gamma(t)\,Z$ (Bất Đẳng Thức Tiếp Diễn Tới Hạn $L^4_t \dot{H}^1_x$):**
* Từ $\frac{dZ}{dt} \le c_\nu Z(t)^3 = \big(c_\nu Z(t)^2\big)\,Z(t)$, đặt hàm nhân tích phân $\mu(t) = \exp\!\left(-c_\nu \int_0^t Z(s)^2\,ds\right)$.
* Chứng minh đạo hàm của $\mu(t) Z(t)$ không dương trên $[0, T]$:

$$Z(T) \le Z(0) \exp\!\left(\frac{169}{8\pi^4\nu^3} \int_0^T Z(s)^2\,ds\right).$$


* **Ý nghĩa ("hạ cấp ngòi nổ"):** thay vì để $Z^3$ bùng nổ phi tuyến, chỉ cần "tích phân quan sát" $\int_0^T Z(s)^2\,ds$ (chuẩn bất biến co giãn $L^4_t \dot{H}^1_x$) bị chặn, toàn bộ ngòi nổ co về chặn mũ bậc nhất theo $Z(0)$.


2. **Định lý 9A2-2 — Chặn Tích Phân Palinstrophy Qua Chuẩn Tới Hạn $L^4_t \dot{H}^1_x$:**
* Kết hợp $\frac{dZ}{dt} \le -\frac{\nu}{4} P(t) + c_\nu Z(t)^3$ với Định lý 9A2-1 trên $[0, T]$:

$$Z(T) + \frac{\nu}{4} \int_0^T P(s)\,ds \le Z(0) + c_\nu \left(\sup_{s \in [0, T]} Z(s)\right) \int_0^T Z(s)^2\,ds.$$


* **Ý nghĩa:** kiểm soát được chuẩn tới hạn $L^4_t \dot{H}^1_x$ là kéo theo đồng thời chặn được cả $\int_0^T P(s)\,ds$ và chuẩn $H^2$, mở đường nối tiếp diễn.


3. **Định lý 9A2-3 — Bước Nhảy "Không Rời Mắt Khỏi Chiếc Lá" (Thời Gian An Toàn Địa Phương Tường Minh):**
* Xét hàm $g(t) = \exp\!\left(-2 c_\nu Z(0)^2 t\right)$ hoặc chặn trực tiếp từ $\dot{Z} \le c_\nu Z^3$: trên mọi đoạn $[0, T]$ với $T < T_{\mathrm{local}}(Z_0, \nu) := \frac{1}{2 c_\nu Z(0)^2} = \frac{4\pi^4\nu^3}{169\, Z(0)^2}$:

$$Z(t) \le \frac{Z(0)}{\sqrt{1 - 2 c_\nu Z(0)^2 t}} \quad \Longleftrightarrow \quad Z(t)^2 \le \frac{Z(0)^2}{1 - 2 c_\nu Z(0)^2 t}.$$


* **Ý nghĩa:** đây chính là thước đo an toàn để chia nhỏ đoạn thác $[0, T_{\mathrm{trap}}]$ thành từng bước $\Delta t_k$ không để "chiếc lá" vượt quá ngưỡng mất kiểm soát trong một bước.


4. **Định lý 9A2-4 — Hợp Nhất 9A1 + 9A2 (Chặn Trên Thời Gian Nổ $T_{\mathrm{trap}}$ & Ranh Giới Mở):**
* Kết luận thống nhất: nếu nghiệm sống sót vượt $T_{\mathrm{trap}} = \frac{13 E_0}{4\pi^3\nu^3}$, nó đi vào bồn hút $H^1$, suy giảm theo hàm mũ về $0$, và cả $\int_0^\infty Z(s)^2\,ds$ lẫn $\int_0^\infty P(s)\,ds$ đều hữu hạn toàn cục.
* Ghi rõ ranh giới mở (đúng tinh thần trung thực học thuật): phần còn lại cho dữ liệu lớn tùy ý nằm ở việc chứng minh $\int_0^{T_{\mathrm{trap}}} Z(s)^2\,ds < \infty$ (hoặc chặn $Z$ không vượt quá mốc chạm bẫy) trên đoạn hữu hạn $[0, T_{\mathrm{trap}}]$.



---

3 Cửa ẢI Đằng Sau Mốc 9 (Trong Chuỗi Mắt Xích Liên Kết)Nguyên tắc mắt xích: Mốc 9 (siết chặt cơ chế bùng nổ / bẫy / tiếp diễn ở vùng siêu tới hạn trên $\mathbb{T}^3$) là điểm thắt cổ chai quyết định. Chỉ khi mắt xích này đủ chặt thì 3 cửa ải sau mới có cơ sở mở khóa; ngược lại, nếu đứt gãy ở Mốc 9 thì xác suất qua các cửa ải sau gần như bằng $0$.1. Cửa ải Mở rộng Miền Không Gian ($\mathbb{T}^3 \longrightarrow \mathbb{R}^3$)Bản chất: Toàn bộ chuỗi Mốc 1–8B và Mốc 9 đang đặt trên hình xuyến tuần hoàn 3 chiều $\mathbb{T}^3 = (\mathbb{R}/\mathbb{Z})^3$. Khi chuyển sang toàn không gian $\mathbb{R}^3$ (với điều kiện suy giảm ở vô cực theo chuẩn phát biểu của bài toán), lưới tần số rời rạc và tính compact của $\mathbb{T}^3$ không còn như cũ.   Mắt nối với Mốc 9: Phải giữ được cơ chế kiểm soát kéo giãn xoáy, tiêu tán nhớt và tiếp diễn nghiệm mà không dựa vào các tính chất riêng có của $\mathbb{T}^3$, đồng thời xử lý trọn vẹn tích phân trên toàn $\mathbb{R}^3$.2. Cửa ải Khép Kín "Tồn Tại Nghiệm" & "Tính Trơn Tru $C^\infty$ Toàn Cục"Bản chất: Nhiều mệnh đề trong vùng bẫy hoặc vùng điều kiện có dạng: nếu nghiệm thỏa mãn điều kiện / tồn tại trên một khoảng thời gian thì mở rộng mượt toàn cục trên $[0, \infty)$. Ở tầng cao nhất, cần khép kín hoàn toàn việc với mọi dữ liệu ban đầu hợp lệ $u_0$, nghiệm mượt $C^\infty$ luôn tồn tại thực sự trên toàn $[0, \infty)$ mà không bị đứt gãy, nổ tung hay rẽ nhánh sang nghiệm yếu bất thường.   Mắt nối với Mốc 9: Bất kỳ chặn tiên nghiệm hay bẫy thời gian nào ở Mốc 9 chỉ thực sự khép kín toàn cục khi nối liền được từ dữ liệu đầu lớn tùy ý vào khoảng thời gian an toàn mà không để sót kẽ hở nào ở giữa.3. Cửa ải Thẩm Định Toán Học & Học Thuật Độc LậpBản chất: Lean 4 / Mathlib4 kiểm chứng chặt chẽ từng bước suy diễn nội tại trong mã (với 0 sorryAx và tách bạch rõ ràng phần vô điều kiện / có điều kiện), nhưng hội đồng thẩm định độc lập sẽ soi từng chân kẽ bên ngoài mã: từ định nghĩa không gian hàm, điều kiện biên/ban đầu, tính khớp của mô hình vật lý–toán học với phát biểu gốc, cho tới từng bước ước lượng trong bài báo.   Mắt nối với Mốc 9: Mốc 9 càng siết chặt từng bất đẳng thức, từng miền giá trị và từng mắt xích suy luận bao nhiêu thì khi bị soi từng chân kẽ ở cửa ải thẩm định, lập luận càng đứng vững bấy nhiêu.