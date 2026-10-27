import tkinter as tk
from tkinter import ttk, messagebox
import time

# ===================== 常量定义 =====================
# S-AES标准S盒（4x4）
SBOX = [
    [9, 4, 10, 11],
    [13, 1, 8, 5],
    [6, 2, 0, 3],
    [12, 14, 15, 7]
]

# S-AES标准逆S盒
INV_SBOX = [
    [10, 5, 9, 11],
    [1, 7, 8, 15],
    [6, 0, 2, 3],
    [12, 4, 13, 14]
]

# 列混合矩阵GF(2^4)系数
MIX_MATRIX = [[1, 4], [4, 1]]
INV_MIX_MATRIX = [[9, 2], [2, 9]]


# ===================== 基础运算工具 =====================
def gf_mult(a, b):
    """
    GF(2^4)有限域乘法，模不可约多项式 x^4 + x + 1
    :param a: 4位整数 0-15
    :param b: 4位整数 0-15
    :return: 乘积结果 0-15
    """
    result = 0
    for _ in range(4):
        if b & 1:
            result ^= a
        carry = a & 0b1000
        a = (a << 1) & 0b1111
        if carry:
            a ^= 0b0011  # x^4 mod x^4+x+1 = x+1
        b >>= 1
    return result


def sub_nib(byte):
    """8位字节的半字节替换（S盒）"""
    high = (byte >> 4) & 0xF
    low = byte & 0xF
    s_high = SBOX[high >> 2][high & 0b11]
    s_low = SBOX[low >> 2][low & 0b11]
    return (s_high << 4) | s_low


def inv_sub_nib(byte):
    """8位字节的逆半字节替换（逆S盒）"""
    high = (byte >> 4) & 0xF
    low = byte & 0xF
    s_high = INV_SBOX[high >> 2][high & 0b11]
    s_low = INV_SBOX[low >> 2][low & 0b11]
    return (s_high << 4) | s_low


def rot_nib(byte):
    """8位字节循环左移4位（高低半字节交换）"""
    return ((byte << 4) | (byte >> 4)) & 0xFF


def bin_str_to_int(bin_str):
    """二进制字符串转整数，自动过滤换行、空格"""
    clean = bin_str.replace(' ', '').replace('\n', '').replace('\r', '')
    return int(clean, 2)


def int_to_bin_str(value, length):
    """整数转指定长度二进制字符串，高位补零"""
    return format(value, f'0{length}b')


# ===================== 密钥扩展模块 =====================
def key_expansion(key_16):
    """
    16位密钥扩展，生成3个16位轮密钥
    :param key_16: 16位原始密钥整数
    :return: k0, k1, k2 三个轮密钥
    """
    w0 = (key_16 >> 8) & 0xFF
    w1 = key_16 & 0xFF
    RCON1 = 0x80
    RCON2 = 0x30

    # 生成w2 w3
    rot_w1 = rot_nib(w1)
    sub_rot_w1 = sub_nib(rot_w1)
    w2 = w0 ^ RCON1 ^ sub_rot_w1
    w3 = w2 ^ w1

    # 生成w4 w5
    rot_w3 = rot_nib(w3)
    sub_rot_w3 = sub_nib(rot_w3)
    w4 = w2 ^ RCON2 ^ sub_rot_w3
    w5 = w4 ^ w3

    k0 = (w0 << 8) | w1
    k1 = (w2 << 8) | w3
    k2 = (w4 << 8) | w5
    return k0, k1, k2


# ===================== 核心单组加解密 =====================
def encrypt_block(plain_16, key_16):
    """
    单组16位明文S-AES加密
    :param plain_16: 16位明文整数
    :param key_16: 16位密钥整数
    :return: 16位密文整数
    """
    k0, k1, k2 = key_expansion(key_16)
    state = plain_16 ^ k0

    # ========== 第1轮 ==========
    # 半字节替换
    high = (state >> 8) & 0xFF
    low = state & 0xFF
    state = (sub_nib(high) << 8) | sub_nib(low)

    # 行移位：第二行左移1个半字节
    high = (state >> 8) & 0xFF
    low = state & 0xFF
    state = (high << 8) | rot_nib(low)

    # 列混合
    s00 = (state >> 12) & 0xF
    s01 = (state >> 8) & 0xF
    s10 = (state >> 4) & 0xF
    s11 = state & 0xF

    col0_s0 = gf_mult(1, s00) ^ gf_mult(4, s10)
    col0_s1 = gf_mult(4, s00) ^ gf_mult(1, s10)
    col1_s0 = gf_mult(1, s01) ^ gf_mult(4, s11)
    col1_s1 = gf_mult(4, s01) ^ gf_mult(1, s11)

    state = (col0_s0 << 12) | (col1_s0 << 8) | (col0_s1 << 4) | col1_s1

    # 轮密钥加
    state ^= k1

    # ========== 第2轮（无列混合） ==========
    # 半字节替换
    high = (state >> 8) & 0xFF
    low = state & 0xFF
    state = (sub_nib(high) << 8) | sub_nib(low)

    # 行移位
    high = (state >> 8) & 0xFF
    low = state & 0xFF
    state = (high << 8) | rot_nib(low)

    # 轮密钥加
    state ^= k2

    return state & 0xFFFF


def decrypt_block(cipher_16, key_16):
    """
    单组16位密文S-AES解密
    :param cipher_16: 16位密文整数
    :param key_16: 16位密钥整数
    :return: 16位明文整数
    """
    k0, k1, k2 = key_expansion(key_16)
    state = cipher_16 ^ k2

    # ========== 第2轮逆操作 ==========
    # 逆行移位
    high = (state >> 8) & 0xFF
    low = state & 0xFF
    state = (high << 8) | rot_nib(low)

    # 逆半字节替换
    high = (state >> 8) & 0xFF
    low = state & 0xFF
    state = (inv_sub_nib(high) << 8) | inv_sub_nib(low)

    # 轮密钥加k1
    state ^= k1

    # ========== 第1轮逆操作 ==========
    # 逆列混合
    s00 = (state >> 12) & 0xF
    s01 = (state >> 8) & 0xF
    s10 = (state >> 4) & 0xF
    s11 = state & 0xF

    col0_s0 = gf_mult(9, s00) ^ gf_mult(2, s10)
    col0_s1 = gf_mult(2, s00) ^ gf_mult(9, s10)
    col1_s0 = gf_mult(9, s01) ^ gf_mult(2, s11)
    col1_s1 = gf_mult(2, s01) ^ gf_mult(9, s11)

    state = (col0_s0 << 12) | (col1_s0 << 8) | (col0_s1 << 4) | col1_s1

    # 逆行移位
    high = (state >> 8) & 0xFF
    low = state & 0xFF
    state = (high << 8) | rot_nib(low)

    # 逆半字节替换
    high = (state >> 8) & 0xFF
    low = state & 0xFF
    state = (inv_sub_nib(high) << 8) | inv_sub_nib(low)

    # 轮密钥加k0
    state ^= k0

    return state & 0xFFFF


# ===================== 第3关：ASCII字符串加解密 =====================
def encrypt_string(plain_text, key_str):
    """ASCII字符串加密，输出二进制密文字符串"""
    key = bin_str_to_int(key_str)
    plain_bytes = plain_text.encode('ascii')
    cipher_bits = []

    for i in range(0, len(plain_bytes), 2):
        block = plain_bytes[i:i+2]
        if len(block) < 2:
            block = block + b'\x00' * (2 - len(block))
        plain_16 = (block[0] << 8) | block[1]
        cipher_16 = encrypt_block(plain_16, key)
        cipher_bits.append(int_to_bin_str(cipher_16, 16))

    return ''.join(cipher_bits)


def decrypt_string(cipher_bin_str, key_str):
    """二进制密文字符串解密，输出ASCII明文字符串"""
    key = bin_str_to_int(key_str)
    # 清理所有非01字符
    clean_bin = ''.join(c for c in cipher_bin_str if c in '01')
    plain_bytes = b''

    for i in range(0, len(clean_bin), 16):
        block_str = clean_bin[i:i+16]
        if len(block_str) < 16:
            block_str = block_str.ljust(16, '0')
        cipher_16 = bin_str_to_int(block_str)
        plain_16 = decrypt_block(cipher_16, key)
        plain_bytes += bytes([(plain_16 >> 8) & 0xFF, plain_16 & 0xFF])

    return plain_bytes.rstrip(b'\x00').decode('ascii', errors='replace')


# ===================== 第4关：多重加密 =====================
def double_encrypt(plain_16, key_32):
    """双重加密：32位密钥，C = E(K2, E(K1, P))"""
    k1 = (key_32 >> 16) & 0xFFFF
    k2 = key_32 & 0xFFFF
    mid = encrypt_block(plain_16, k1)
    return encrypt_block(mid, k2)


def double_decrypt(cipher_16, key_32):
    """双重解密：32位密钥，P = D(K1, D(K2, C))"""
    k1 = (key_32 >> 16) & 0xFFFF
    k2 = key_32 & 0xFFFF
    mid = decrypt_block(cipher_16, k2)
    return decrypt_block(mid, k1)


def meet_in_the_middle(plain_16, cipher_16):
    """
    中间相遇攻击：已知明密文对，找出所有匹配的(K1, K2)密钥对
    :return: (密钥对列表, 耗时秒数)
    """
    start_time = time.time()
    # 前向加密表：{中间值: [K1列表]}
    forward_table = {}
    for k1 in range(0x10000):
        mid_val = encrypt_block(plain_16, k1)
        if mid_val in forward_table:
            forward_table[mid_val].append(k1)
        else:
            forward_table[mid_val] = [k1]

    # 后向解密匹配
    found_keys = []
    for k2 in range(0x10000):
        mid_val = decrypt_block(cipher_16, k2)
        if mid_val in forward_table:
            for k1 in forward_table[mid_val]:
                found_keys.append((k1, k2))

    elapsed = time.time() - start_time
    return found_keys, elapsed


def triple_encrypt(plain_16, key_32):
    """三重加密（32位密钥EDE模式）：C = E(K1, D(K2, E(K1, P)))"""
    k1 = (key_32 >> 16) & 0xFFFF
    k2 = key_32 & 0xFFFF
    step1 = encrypt_block(plain_16, k1)
    step2 = decrypt_block(step1, k2)
    return encrypt_block(step2, k1)


def triple_decrypt(cipher_16, key_32):
    """三重解密（32位密钥EDE模式）"""
    k1 = (key_32 >> 16) & 0xFFFF
    k2 = key_32 & 0xFFFF
    step1 = decrypt_block(cipher_16, k1)
    step2 = encrypt_block(step1, k2)
    return decrypt_block(step2, k1)


# ===================== 第5关：CBC工作模式 =====================
def cbc_encrypt(plain_text, key_str, iv_str):
    """CBC模式加密，返回二进制密文字符串和密文分组列表"""
    key = bin_str_to_int(key_str)
    iv = bin_str_to_int(iv_str)
    plain_bytes = plain_text.encode('ascii')
    cipher_blocks = []
    prev_cipher = iv

    for i in range(0, len(plain_bytes), 2):
        block = plain_bytes[i:i+2]
        if len(block) < 2:
            block = block + b'\x00' * (2 - len(block))
        plain_16 = (block[0] << 8) | block[1]
        # 与前一组密文异或
        plain_xor = plain_16 ^ prev_cipher
        cipher_16 = encrypt_block(plain_xor, key)
        cipher_blocks.append(cipher_16)
        prev_cipher = cipher_16

    cipher_bin = ''.join(int_to_bin_str(c, 16) for c in cipher_blocks)
    return cipher_bin, cipher_blocks


def cbc_decrypt(cipher_bin_str, key_str, iv_str):
    """CBC模式解密"""
    key = bin_str_to_int(key_str)
    iv = bin_str_to_int(iv_str)
    clean_bin = ''.join(c for c in cipher_bin_str if c in '01')
    plain_bytes = b''
    prev_cipher = iv

    for i in range(0, len(clean_bin), 16):
        block_str = clean_bin[i:i+16]
        if len(block_str) < 16:
            block_str = block_str.ljust(16, '0')
        cipher_16 = bin_str_to_int(block_str)
        plain_xor = decrypt_block(cipher_16, key)
        plain_16 = plain_xor ^ prev_cipher
        plain_bytes += bytes([(plain_16 >> 8) & 0xFF, plain_16 & 0xFF])
        prev_cipher = cipher_16

    return plain_bytes.rstrip(b'\x00').decode('ascii', errors='replace')


# ===================== GUI 图形界面 =====================
class SAESApp:
    def __init__(self, root):
        self.root = root
        self.root.title("S-AES 加密解密工具")
        self.root.geometry("700x600")

        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill='both', expand=True, padx=10, pady=10)

        self._init_basic_tab()
        self._init_ascii_tab()
        self._init_multi_tab()
        self._init_cbc_tab()

    def _init_basic_tab(self):
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text='基本测试')

        ttk.Label(frame, text='16位明文/密文 (二进制):').grid(row=0, column=0, padx=5, pady=12, sticky='w')
        self.entry_plain = ttk.Entry(frame, width=40)
        self.entry_plain.grid(row=0, column=1, padx=5, pady=12)
        self.entry_plain.insert(0, '1010101010101010')

        ttk.Label(frame, text='16位密钥 (二进制):').grid(row=1, column=0, padx=5, pady=12, sticky='w')
        self.entry_key = ttk.Entry(frame, width=40)
        self.entry_key.grid(row=1, column=1, padx=5, pady=12)
        self.entry_key.insert(0, '0010110101001001')

        btn_frame = ttk.Frame(frame)
        btn_frame.grid(row=2, column=0, columnspan=2, pady=10)
        ttk.Button(btn_frame, text='加密', command=self._encrypt_basic).pack(side='left', padx=10)
        ttk.Button(btn_frame, text='解密', command=self._decrypt_basic).pack(side='left', padx=10)

        ttk.Label(frame, text='运算结果:').grid(row=3, column=0, padx=5, pady=12, sticky='w')
        self.label_result = ttk.Label(frame, text='', foreground='#0066cc', font=('微软雅黑', 10, 'bold'))
        self.label_result.grid(row=3, column=1, padx=5, pady=12, sticky='w')

    def _encrypt_basic(self):
        plain_str = self.entry_plain.get().strip()
        key_str = self.entry_key.get().strip()
        if not self._check_bit_len(plain_str, 16) or not self._check_bit_len(key_str, 16):
            return
        plain = bin_str_to_int(plain_str)
        key = bin_str_to_int(key_str)
        cipher = encrypt_block(plain, key)
        self.label_result.config(text=f'密文: {int_to_bin_str(cipher, 16)}')

    def _decrypt_basic(self):
        cipher_str = self.entry_plain.get().strip()
        key_str = self.entry_key.get().strip()
        if not self._check_bit_len(cipher_str, 16) or not self._check_bit_len(key_str, 16):
            return
        cipher = bin_str_to_int(cipher_str)
        key = bin_str_to_int(key_str)
        plain = decrypt_block(cipher, key)
        self.label_result.config(text=f'明文: {int_to_bin_str(plain, 16)}')

    def _init_ascii_tab(self):
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text='ASCII加密')

        ttk.Label(frame, text='明文字符串 (ASCII):').grid(row=0, column=0, padx=5, pady=10, sticky='nw')
        self.text_plain = tk.Text(frame, height=4, width=50)
        self.text_plain.grid(row=0, column=1, padx=5, pady=10)
        self.text_plain.insert('1.0', 'Hello S-AES')

        ttk.Label(frame, text='16位密钥 (二进制):').grid(row=1, column=0, padx=5, pady=10, sticky='w')
        self.entry_key_ascii = ttk.Entry(frame, width=40)
        self.entry_key_ascii.grid(row=1, column=1, padx=5, pady=10, sticky='w')
        self.entry_key_ascii.insert(0, '0010110101001001')

        btn_frame = ttk.Frame(frame)
        btn_frame.grid(row=2, column=0, columnspan=2, pady=8)
        ttk.Button(btn_frame, text='加密', command=self._encrypt_ascii).pack(side='left', padx=10)
        ttk.Button(btn_frame, text='解密', command=self._decrypt_ascii).pack(side='left', padx=10)

        ttk.Label(frame, text='二进制密文:').grid(row=3, column=0, padx=5, pady=10, sticky='nw')
        self.text_cipher_bin = tk.Text(frame, height=4, width=50)
        self.text_cipher_bin.grid(row=3, column=1, padx=5, pady=10)

        ttk.Label(frame, text='解密结果:').grid(row=4, column=0, padx=5, pady=10, sticky='nw')
        self.text_decrypt = tk.Text(frame, height=4, width=50)
        self.text_decrypt.grid(row=4, column=1, padx=5, pady=10)

    def _encrypt_ascii(self):
        plain_text = self.text_plain.get('1.0', 'end').strip()
        key_str = self.entry_key_ascii.get().strip()
        if not self._check_bit_len(key_str, 16):
            return
        cipher_bin = encrypt_string(plain_text, key_str)
        self.text_cipher_bin.delete('1.0', 'end')
        self.text_cipher_bin.insert('1.0', cipher_bin)

    def _decrypt_ascii(self):
        cipher_bin = self.text_cipher_bin.get('1.0', 'end').strip()
        key_str = self.entry_key_ascii.get().strip()
        if not self._check_bit_len(key_str, 16):
            return
        # 校验是否有有效二进制内容
        clean_bin = ''.join(c for c in cipher_bin if c in '01')
        if len(clean_bin) == 0:
            messagebox.showerror('错误', '二进制密文框为空，请先加密或输入有效密文')
            return
        plain_text = decrypt_string(cipher_bin, key_str)
        self.text_decrypt.delete('1.0', 'end')
        self.text_decrypt.insert('1.0', plain_text)

    def _init_multi_tab(self):
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text='多重加密')

        # 双重加密区域
        ttk.Label(frame, text='--- 双重加密 (32位密钥) ---', font=('微软雅黑', 10, 'bold')).grid(row=0, column=0, columnspan=2, pady=8)
        ttk.Label(frame, text='16位明文:').grid(row=1, column=0, padx=5, pady=6, sticky='w')
        self.entry_double_plain = ttk.Entry(frame, width=40)
        self.entry_double_plain.grid(row=1, column=1, padx=5, pady=6)
        self.entry_double_plain.insert(0, '1010101010101010')

        ttk.Label(frame, text='32位密钥:').grid(row=2, column=0, padx=5, pady=6, sticky='w')
        self.entry_double_key = ttk.Entry(frame, width=40)
        self.entry_double_key.grid(row=2, column=1, padx=5, pady=6)
        self.entry_double_key.insert(0, '00101101010010011101011100101100')

        btn_frame1 = ttk.Frame(frame)
        btn_frame1.grid(row=3, column=0, columnspan=2, pady=6)
        ttk.Button(btn_frame1, text='双重加密', command=self._run_double_encrypt).pack(side='left', padx=10)
        ttk.Button(btn_frame1, text='双重解密', command=self._run_double_decrypt).pack(side='left', padx=10)

        self.label_double_result = ttk.Label(frame, text='', foreground='#0066cc')
        self.label_double_result.grid(row=4, column=0, columnspan=2, pady=6)

        # 中间相遇攻击区域
        ttk.Label(frame, text='--- 中间相遇攻击 ---', font=('微软雅黑', 10, 'bold')).grid(row=5, column=0, columnspan=2, pady=10)
        ttk.Label(frame, text='已知明文:').grid(row=6, column=0, padx=5, pady=6, sticky='w')
        self.entry_mitm_plain = ttk.Entry(frame, width=40)
        self.entry_mitm_plain.grid(row=6, column=1, padx=5, pady=6)
        self.entry_mitm_plain.insert(0, '1010101010101010')

        ttk.Label(frame, text='已知密文:').grid(row=7, column=0, padx=5, pady=6, sticky='w')
        self.entry_mitm_cipher = ttk.Entry(frame, width=40)
        self.entry_mitm_cipher.grid(row=7, column=1, padx=5, pady=6)

        ttk.Button(frame, text='开始攻击', command=self._run_mitm).grid(row=8, column=0, columnspan=2, pady=8)

        ttk.Label(frame, text='攻击结果:').grid(row=9, column=0, padx=5, pady=6, sticky='nw')
        self.text_mitm_result = tk.Text(frame, height=6, width=55)
        self.text_mitm_result.grid(row=9, column=1, padx=5, pady=6)

        # 三重加密区域
        ttk.Label(frame, text='--- 三重加密 (32位密钥EDE模式) ---', font=('微软雅黑', 10, 'bold')).grid(row=10, column=0, columnspan=2, pady=10)
        btn_frame2 = ttk.Frame(frame)
        btn_frame2.grid(row=11, column=0, columnspan=2, pady=6)
        ttk.Button(btn_frame2, text='三重加密', command=self._run_triple_encrypt).pack(side='left', padx=10)
        ttk.Button(btn_frame2, text='三重解密', command=self._run_triple_decrypt).pack(side='left', padx=10)

        self.label_triple_result = ttk.Label(frame, text='', foreground='#0066cc')
        self.label_triple_result.grid(row=12, column=0, columnspan=2, pady=6)

    def _run_double_encrypt(self):
        plain_str = self.entry_double_plain.get().strip()
        key_str = self.entry_double_key.get().strip()
        if not self._check_bit_len(plain_str, 16) or not self._check_bit_len(key_str, 32):
            return
        plain = bin_str_to_int(plain_str)
        key = bin_str_to_int(key_str)
        cipher = double_encrypt(plain, key)
        self.label_double_result.config(text=f'双重加密结果: {int_to_bin_str(cipher, 16)}')

    def _run_double_decrypt(self):
        cipher_str = self.entry_double_plain.get().strip()
        key_str = self.entry_double_key.get().strip()
        if not self._check_bit_len(cipher_str, 16) or not self._check_bit_len(key_str, 32):
            return
        cipher = bin_str_to_int(cipher_str)
        key = bin_str_to_int(key_str)
        plain = double_decrypt(cipher, key)
        self.label_double_result.config(text=f'双重解密结果: {int_to_bin_str(plain, 16)}')

    def _run_mitm(self):
        plain_str = self.entry_mitm_plain.get().strip()
        cipher_str = self.entry_mitm_cipher.get().strip()
        if not self._check_bit_len(plain_str, 16) or not self._check_bit_len(cipher_str, 16):
            return
        plain = bin_str_to_int(plain_str)
        cipher = bin_str_to_int(cipher_str)
        found, elapsed = meet_in_the_middle(plain, cipher)
        self.text_mitm_result.delete('1.0', 'end')
        self.text_mitm_result.insert('1.0', f'总耗时: {elapsed:.2f} 秒\n共找到 {len(found)} 组密钥对:\n')
        for k1, k2 in found[:10]:
            self.text_mitm_result.insert('end', f'  K1={int_to_bin_str(k1,16)}  K2={int_to_bin_str(k2,16)}\n')
        if len(found) > 10:
            self.text_mitm_result.insert('end', f'... 剩余 {len(found)-10} 组未展示\n')

    def _run_triple_encrypt(self):
        plain_str = self.entry_double_plain.get().strip()
        key_str = self.entry_double_key.get().strip()
        if not self._check_bit_len(plain_str, 16) or not self._check_bit_len(key_str, 32):
            return
        plain = bin_str_to_int(plain_str)
        key = bin_str_to_int(key_str)
        cipher = triple_encrypt(plain, key)
        self.label_triple_result.config(text=f'三重加密结果: {int_to_bin_str(cipher, 16)}')

    def _run_triple_decrypt(self):
        cipher_str = self.entry_double_plain.get().strip()
        key_str = self.entry_double_key.get().strip()
        if not self._check_bit_len(cipher_str, 16) or not self._check_bit_len(key_str, 32):
            return
        cipher = bin_str_to_int(cipher_str)
        key = bin_str_to_int(key_str)
        plain = triple_decrypt(cipher, key)
        self.label_triple_result.config(text=f'三重解密结果: {int_to_bin_str(plain, 16)}')

    def _init_cbc_tab(self):
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text='CBC模式')

        ttk.Label(frame, text='明文字符串:').grid(row=0, column=0, padx=5, pady=8, sticky='nw')
        self.text_cbc_plain = tk.Text(frame, height=3, width=50)
        self.text_cbc_plain.grid(row=0, column=1, padx=5, pady=8)
        self.text_cbc_plain.insert('1.0', 'CBC mode test')

        ttk.Label(frame, text='16位密钥:').grid(row=1, column=0, padx=5, pady=8, sticky='w')
        self.entry_cbc_key = ttk.Entry(frame, width=40)
        self.entry_cbc_key.grid(row=1, column=1, padx=5, pady=8, sticky='w')
        self.entry_cbc_key.insert(0, '0010110101001001')

        ttk.Label(frame, text='16位初始向量IV:').grid(row=2, column=0, padx=5, pady=8, sticky='w')
        self.entry_cbc_iv = ttk.Entry(frame, width=40)
        self.entry_cbc_iv.grid(row=2, column=1, padx=5, pady=8, sticky='w')
        self.entry_cbc_iv.insert(0, '1111000011110000')

        btn_frame = ttk.Frame(frame)
        btn_frame.grid(row=3, column=0, columnspan=2, pady=8)
        ttk.Button(btn_frame, text='CBC加密', command=self._run_cbc_encrypt).pack(side='left', padx=10)
        ttk.Button(btn_frame, text='CBC解密', command=self._run_cbc_decrypt).pack(side='left', padx=10)
        ttk.Button(btn_frame, text='篡改测试', command=self._run_cbc_tamper).pack(side='left', padx=10)

        ttk.Label(frame, text='二进制密文:').grid(row=4, column=0, padx=5, pady=8, sticky='nw')
        self.text_cbc_cipher = tk.Text(frame, height=3, width=50)
        self.text_cbc_cipher.grid(row=4, column=1, padx=5, pady=8)

        ttk.Label(frame, text='解密结果:').grid(row=5, column=0, padx=5, pady=8, sticky='nw')
        self.text_cbc_decrypt = tk.Text(frame, height=3, width=50)
        self.text_cbc_decrypt.grid(row=5, column=1, padx=5, pady=8)

        ttk.Label(frame, text='篡改后解密结果:').grid(row=6, column=0, padx=5, pady=8, sticky='nw')
        self.text_cbc_tamper = tk.Text(frame, height=3, width=50)
        self.text_cbc_tamper.grid(row=6, column=1, padx=5, pady=8)

    def _run_cbc_encrypt(self):
        plain_text = self.text_cbc_plain.get('1.0', 'end').strip()
        key_str = self.entry_cbc_key.get().strip()
        iv_str = self.entry_cbc_iv.get().strip()
        if not self._check_bit_len(key_str, 16) or not self._check_bit_len(iv_str, 16):
            return
        cipher_bin, _ = cbc_encrypt(plain_text, key_str, iv_str)
        self.text_cbc_cipher.delete('1.0', 'end')
        self.text_cbc_cipher.insert('1.0', cipher_bin)

    def _run_cbc_decrypt(self):
        cipher_bin = self.text_cbc_cipher.get('1.0', 'end').strip()
        key_str = self.entry_cbc_key.get().strip()
        iv_str = self.entry_cbc_iv.get().strip()
        if not self._check_bit_len(key_str, 16) or not self._check_bit_len(iv_str, 16):
            return
        plain_text = cbc_decrypt(cipher_bin, key_str, iv_str)
        self.text_cbc_decrypt.delete('1.0', 'end')
        self.text_cbc_decrypt.insert('1.0', plain_text)

    def _run_cbc_tamper(self):
        """篡改第一组密文的第一位，测试解密结果"""
        cipher_bin = self.text_cbc_cipher.get('1.0', 'end').strip()
        key_str = self.entry_cbc_key.get().strip()
        iv_str = self.entry_cbc_iv.get().strip()
        clean_bin = ''.join(c for c in cipher_bin if c in '01')
        if not clean_bin or not self._check_bit_len(key_str, 16) or not self._check_bit_len(iv_str, 16):
            messagebox.showerror('错误', '请先执行CBC加密生成密文')
            return
        # 翻转第一位
        tampered = list(clean_bin)
        tampered[0] = '1' if tampered[0] == '0' else '0'
        tampered_bin = ''.join(tampered)
        plain_text = cbc_decrypt(tampered_bin, key_str, iv_str)
        self.text_cbc_tamper.delete('1.0', 'end')
        self.text_cbc_tamper.insert('1.0', plain_text)

    # 输入校验辅助函数
    def _check_bit_len(self, s, length):
        clean = ''.join(c for c in s if c in '01')
        if len(clean) != length:
            messagebox.showerror('错误', f'必须输入{length}位二进制字符串')
            return False
        return True


if __name__ == '__main__':
    root = tk.Tk()
    app = SAESApp(root)
    root.mainloop()
