#include <bits/stdc++.h>

typedef long long ll;

using namespace std;
using cpx = complex<double>;
const double PI = acos(-1);
vector<cpx> roots = {{0, 0}, {1, 0}};
static ll p;

void ensure_capacity(ll min_capacity) {
    for (ll len = roots.size(); len < min_capacity; len *= 2) {
        for (ll i = len >> 1; i < len; i++) {
            roots.emplace_back(roots[i]);
            double angle = 2 * PI * (2 * i + 1 - len) / (len * 2);
            roots.emplace_back(cos(angle), sin(angle));
        }
    }
}

void fft(vector<cpx> &z, bool inverse) {
    ll n = z.size();
    ensure_capacity(n);
    for (unsigned i = 1, j = 0; i < n; i++) {
        ll bit = n >> 1;
        for (; j >= bit; bit >>= 1)
            j -= bit;
        j += bit;
        if (i < j)
            swap(z[i], z[j]);
    }
    for (ll len = 1; len < n; len <<= 1) {
        for (ll i = 0; i < n; i += len * 2) {
            for (ll j = 0; j < len; j++) {
                cpx root = inverse ? conj(roots[j + len]) : roots[j + len];
                cpx u = z[i + j];
                cpx v = z[i + j + len] * root;
                z[i + j] = u + v;
                z[i + j + len] = u - v;
            }
        }
    }
    if (inverse)
        for (ll i = 0; i < n; i++)
            z[i] /= n;
}

vector<ll> multiply_bigint(const vector<ll> &a, const vector<ll> &b, ll base) {
    ll need = a.size() + b.size();
    ll n = 1;
    while (n < need)
        n <<= 1;
    vector<cpx> p(n);
    for (size_t i = 0; i < n; i++) {
        p[i] = cpx(i < a.size() ? a[i] : 0, i < b.size() ? b[i] : 0);
    }
    fft(p, false);
    vector<cpx> ab(n);
    cpx r(0, -0.25);
    for (ll i = 0; i < n; i++) {
        ll j = (n - i) & (n - 1);
        ab[i] = (p[i] * p[i] - conj(p[j] * p[j])) * r;
    }
    fft(ab, true);
    vector<ll> result(need);
    ll carry = 0;
    for (ll i = 0; i < need; i++) {
        ll d = (ll)(ab[i].real() + 0.5) + carry;
        carry = d / base;
        result[i] = d % base;
    }
    return result;
}

vector<ll> multiply_mod(const vector<ll> &a, const vector<ll> &b, ll m) {
    ll need = a.size() + b.size() - 1;
    ll n = 1;
    while (n < need)
        n <<= 1;
    vector<cpx> A(n);
    for (size_t i = 0; i < a.size(); i++) {
        ll x = (a[i] % m + m) % m;
        A[i] = cpx(x & ((1 << 15) - 1), x >> 15);
    }
    fft(A, false);

    vector<cpx> B(n);
    for (size_t i = 0; i < b.size(); i++) {
        ll x = (b[i] % m + m) % m;
        B[i] = cpx(x & ((1 << 15) - 1), x >> 15);
    }
    fft(B, false);

    vector<cpx> fa(n);
    vector<cpx> fb(n);
    for (ll i = 0, j = 0; i < n; i++, j = n - i) {
        cpx a1 = (A[i] + conj(A[j])) * cpx(0.5, 0);
        cpx a2 = (A[i] - conj(A[j])) * cpx(0, -0.5);
        cpx b1 = (B[i] + conj(B[j])) * cpx(0.5, 0);
        cpx b2 = (B[i] - conj(B[j])) * cpx(0, -0.5);
        fa[i] = a1 * b1 + a2 * b2 * cpx(0, 1);
        fb[i] = a1 * b2 + a2 * b1;
    }

    fft(fa, true);
    fft(fb, true);
    vector<ll> res(need);
    for (ll i = 0; i < need; i++) {
        ll aa = (ll)(fa[i].real() + 0.5);
        ll bb = (ll)(fb[i].real() + 0.5);
        ll cc = (ll)(fa[i].imag() + 0.5);
        res[i] = (aa % m + (bb % m << 15) + (cc % m << 30)) % m;
    }
    return res;
}
constexpr ll digits(ll base) noexcept {
    return base <= 1 ? 0 : 1 + digits(base / 10);
}

constexpr ll base = 1000'000'000;
constexpr ll base_digits = digits(base);

constexpr ll fft_base = 10'000;  // fft_base^2 * n / fft_base_digits <= 10^15 for double
constexpr ll fft_base_digits = digits(fft_base);

struct bigint {
    vector<ll> z = {0};  // digits

    ll sign;

    bigint(ll v = 0) { *this = v; }

    bigint &operator=(ll v) {
        sign = v < 0 ? -1 : 1;
        v *= sign;
        z.clear();
        for (; v > 0; v = v / base)
            z.push_back((ll)(v % base));
        return *this;
    }

    bigint(const string &s) { read(s); }

    bigint &operator+=(const bigint &other) {
        if (sign == other.sign) {
            for (ll i = 0, carry = 0; i < other.z.size() || carry; ++i) {
                if (i == z.size())
                    z.push_back(0);
                z[i] += carry + (i < other.z.size() ? other.z[i] : 0);
                carry = z[i] >= base;
                if (carry)
                    z[i] -= base;
            }
        } else if (other != 0 /* prevent infinite loop */) {
            *this -= -other;
        }
        return *this;
    }

    friend bigint operator+(bigint a, const bigint &b) {
        a += b;
        return a;
    }

    bigint &operator-=(const bigint &other) {
        if (sign == other.sign) {
            if ((sign == 1 && *this >= other) || (sign == -1 && *this <= other)) {
                for (ll i = 0, carry = 0; i < other.z.size() || carry; ++i) {
                    z[i] -= carry + (i < other.z.size() ? other.z[i] : 0);
                    carry = z[i] < 0;
                    if (carry)
                        z[i] += base;
                }
                trim();
            } else {
                *this = other - *this;
                this->sign = -this->sign;
            }
        } else {
            *this += -other;
        }
        return *this;
    }

    friend bigint operator-(bigint a, const bigint &b) {
        a -= b;
        return a;
    }

    bigint &operator*=(ll v) {
        if (v < 0)
            sign = -sign, v = -v;
        for (ll i = 0, carry = 0; i < z.size() || carry; ++i) {
            if (i == z.size())
                z.push_back(0);
            ll cur = (ll)z[i] * v + carry;
            carry = (ll)(cur / base);
            z[i] = (ll)(cur % base);
        }
        trim();
        return *this;
    }

    bigint operator*(ll v) const { return bigint(*this) *= v; }

    friend pair<bigint, bigint> divmod(const bigint &a1, const bigint &b1) {
        ll norm = base / (b1.z.back() + 1);
        bigint a = a1.abs() * norm;
        bigint b = b1.abs() * norm;
        bigint q, r;
        q.z.resize(a.z.size());

        for (ll i = (ll)a.z.size() - 1; i >= 0; i--) {
            r *= base;
            r += a.z[i];
            ll s1 = b.z.size() < r.z.size() ? r.z[b.z.size()] : 0;
            ll s2 = b.z.size() - 1 < r.z.size() ? r.z[b.z.size() - 1] : 0;
            ll d = (ll)(((ll)s1 * base + s2) / b.z.back());
            r -= b * d;
            while (r < 0)
                r += b, --d;
            q.z[i] = d;
        }

        q.sign = a1.sign * b1.sign;
        r.sign = a1.sign;
        q.trim();
        r.trim();
        return {q, r / norm};
    }

    friend bigint sqrt(const bigint &a1) {
        bigint a = a1;
        while (a.z.empty() || a.z.size() % 2 == 1)
            a.z.push_back(0);

        ll n = a.z.size();

        ll firstDigit = (ll)::sqrt((double)a.z[n - 1] * base + a.z[n - 2]);
        ll norm = base / (firstDigit + 1);
        a *= norm;
        a *= norm;
        while (a.z.empty() || a.z.size() % 2 == 1)
            a.z.push_back(0);

        bigint r = (ll)a.z[n - 1] * base + a.z[n - 2];
        firstDigit = (ll)::sqrt((double)a.z[n - 1] * base + a.z[n - 2]);
        ll q = firstDigit;
        bigint res;

        for (ll j = n / 2 - 1; j >= 0; j--) {
            for (;; --q) {
                bigint r1 = (r - (res * 2 * base + q) * q) * base * base +
                            (j > 0 ? (ll)a.z[2 * j - 1] * base + a.z[2 * j - 2] : 0);
                if (r1 >= 0) {
                    r = r1;
                    break;
                }
            }
            res *= base;
            res += q;

            if (j > 0) {
                ll d1 = res.z.size() + 2 < r.z.size() ? r.z[res.z.size() + 2] : 0;
                ll d2 = res.z.size() + 1 < r.z.size() ? r.z[res.z.size() + 1] : 0;
                ll d3 = res.z.size() < r.z.size() ? r.z[res.z.size()] : 0;
                q = (ll)(((ll)d1 * base * base + (ll)d2 * base + d3) / (firstDigit * 2));
            }
        }

        res.trim();
        return res / norm;
    }

    bigint operator/(const bigint &v) const { return divmod(*this, v).first; }

    bigint operator%(const bigint &v) const { return divmod(*this, v).second; }

    bigint &operator/=(ll v) {
        if (v < 0)
            sign = -sign, v = -v;
        for (ll i = (ll)z.size() - 1, rem = 0; i >= 0; --i) {
            ll cur = z[i] + rem * (ll)base;
            z[i] = (ll)(cur / v);
            rem = (ll)(cur % v);
        }
        trim();
        return *this;
    }

    bigint operator/(ll v) const { return bigint(*this) /= v; }

    ll operator%(ll v) const {
        if (v < 0)
            v = -v;
        ll m = 0;
        for (ll i = (ll)z.size() - 1; i >= 0; --i)
            m = (ll)((z[i] + m * (ll)base) % v);
        return m * sign;
    }

    bigint &operator*=(const bigint &v) {
        *this = *this * v;
        return *this;
    }

    bigint &operator/=(const bigint &v) {
        *this = *this / v;
        return *this;
    }

    bigint &operator%=(const bigint &v) {
        *this = *this % v;
        return *this;
    }

    bool operator<(const bigint &v) const {
        if (sign != v.sign)
            return sign < v.sign;
        if (z.size() != v.z.size())
            return z.size() * sign < v.z.size() * v.sign;
        for (ll i = (ll)z.size() - 1; i >= 0; i--)
            if (z[i] != v.z[i])
                return z[i] * sign < v.z[i] * sign;
        return false;
    }

    bool operator>(const bigint &v) const { return v < *this; }

    bool operator<=(const bigint &v) const { return !(v < *this); }

    bool operator>=(const bigint &v) const { return !(*this < v); }

    bool operator==(const bigint &v) const { return sign == v.sign && z == v.z; }

    bool operator!=(const bigint &v) const { return !(*this == v); }

    void trim() {
        while (!z.empty() && z.back() == 0)
            z.pop_back();
        if (z.empty())
            sign = 1;
    }

    bool isZero() const { return z.empty(); }

    friend bigint operator-(bigint v) {
        if (!v.z.empty())
            v.sign = -v.sign;
        return v;
    }

    bigint abs() const { return sign == 1 ? *this : -*this; }

    ll longValue() const {
        ll res = 0;
        for (ll i = (ll)z.size() - 1; i >= 0; i--)
            res = res * base + z[i];
        return res * sign;
    }

    friend bigint gcd(const bigint &a, const bigint &b) { return b.isZero() ? a : gcd(b, a % b); }

    friend bigint lcm(const bigint &a, const bigint &b) { return a / gcd(a, b) * b; }

    void read(const string &s) {
        sign = 1;
        z.clear();
        ll pos = 0;
        while (pos < s.size() && (s[pos] == '-' || s[pos] == '+')) {
            if (s[pos] == '-')
                sign = -sign;
            ++pos;
        }
        for (ll i = (ll)s.size() - 1; i >= pos; i -= base_digits) {
            ll x = 0;
            for (ll j = max(pos, i - base_digits + 1); j <= i; j++)
                x = x * 10 + s[j] - '0';
            z.push_back(x);
        }
        trim();
    }

    friend istream &operator>>(istream &stream, bigint &v) {
        string s;
        stream >> s;
        v.read(s);
        return stream;
    }

    friend ostream &operator<<(ostream &stream, const bigint &v) {
        if (v.sign == -1)
            stream << '-';
        stream << (v.z.empty() ? 0 : v.z.back());
        for (ll i = (ll)v.z.size() - 2; i >= 0; --i)
            stream << setw(base_digits) << setfill('0') << v.z[i];
        return stream;
    }

    static vector<ll> convert_base(const vector<ll> &a, ll old_digits, ll new_digits) {
        vector<ll> p(max(old_digits, new_digits) + 1);
        p[0] = 1;
        for (ll i = 1; i < p.size(); i++)
            p[i] = p[i - 1] * 10;
        vector<ll> res;
        ll cur = 0;
        ll cur_digits = 0;
        for (ll v : a) {
            cur += v * p[cur_digits];
            cur_digits += old_digits;
            while (cur_digits >= new_digits) {
                res.push_back(ll(cur % p[new_digits]));
                cur /= p[new_digits];
                cur_digits -= new_digits;
            }
        }
        res.push_back((ll)cur);
        while (!res.empty() && res.back() == 0)
            res.pop_back();
        return res;
    }

    bigint operator*(const bigint &v) const {
        if (min(z.size(), v.z.size()) < 150)
            return mul_simple(v);
        bigint res;
        res.sign = sign * v.sign;
        res.z = multiply_bigint(convert_base(z, base_digits, fft_base_digits),
                                convert_base(v.z, base_digits, fft_base_digits), fft_base);
        res.z = convert_base(res.z, fft_base_digits, base_digits);
        res.trim();
        return res;
    }

    bigint mul_simple(const bigint &v) const {
        bigint res;
        res.sign = sign * v.sign;
        res.z.resize(z.size() + v.z.size());
        for (ll i = 0; i < z.size(); ++i)
            if (z[i])
                for (ll j = 0, carry = 0; j < v.z.size() || carry; ++j) {
                    ll cur = res.z[i + j] + (ll)z[i] * (j < v.z.size() ? v.z[j] : 0) + carry;
                    carry = (ll)(cur / base);
                    res.z[i + j] = (ll)(cur % base);
                }
        res.trim();
        return res;
    }
};
// Возведение в степень:
ll pow(ll a, ll n, ll p) {
    ll res(1);
    while (n > 0) {
        if (n % 2 != 0)
            res = (res * a) % p;
        a = (a * a) % p;
        n /= 2;
    }
    return res % p;
}
bigint combine(ll p, const vector<ll>& nums) {
    bigint res(0), shift(1);
    for (const auto& num : nums) {
        res += shift * num;
        shift *= p;
    }
    return res;
}


template<typename T>
struct Polynomial {
    vector<T> data;
    explicit Polynomial(vector<T>&& v) : data(move(v)) {}
    template<typename It>
    explicit Polynomial(const It& begin, const It& end) : data(begin, end) {}

    [[nodiscard]] int Degree() const {
        auto pred = [](const T& x) { return x != static_cast<T>(0); };
        auto i = data.rend() - find_if(data.rbegin(), data.rend(), pred);
        return (i ? i - 1 : -1);
    }
    Polynomial&operator+=(const Polynomial& other) {
        data.resize(max(other.Degree(), Degree()) + 1);
        for (size_t i = 0; i < data.size(); ++i) {
            data[i] = (data[i] + other[i]) % p;
        }
        return *this;
    }
    friend Polynomial operator+(Polynomial first, const Polynomial& second) {
        return move(first += second);
    }
    Polynomial&operator-=(const Polynomial& other) {
        data.resize(max(other.Degree(), Degree()) + 1);
        for (size_t i = 0; i < data.size(); ++i) {
            data[i] = (data[i] - other[i]) % p;
        }
        return *this;
    }
    friend Polynomial operator-(Polynomial first, const Polynomial& second) {
        return move(first -= second);
    }
    friend bool operator!=(const Polynomial& first, const Polynomial& second) {
        return !(first == second);
    }
    T operator[](size_t i) const {
        return (i >= data.size() ? static_cast<T>(0) : data[i]);
    }
    Polynomial& operator*=(const Polynomial& other) {
        auto s1 = Degree() + 1;
        auto s2 = other.Degree() + 1;
        if (s2 == 0) {
            data = {static_cast<T>(0)};
            return *this;
        } else if (s1 == 0) {
            return *this;
        }
        vector<T> ans(s1 + s2 - 1);
        for (ll i = 0; i < s1; ++i) {
            for (ll j = 0; j < s2; ++j) {
                ans[i + j] = (ans[i + j] + data[i] * other.data[j]) % p;
            }
        }
        data = move(ans);
        return *this;
    }
    friend Polynomial operator*(Polynomial first, const Polynomial& second) {
        return move(first *= second);
    }
    friend Polynomial<T> operator/(Polynomial first, Polynomial second) {
        auto s1 = first.Degree();
        auto s2 = second.Degree();
        if (s1 == -1 || s2 == -1 || s1 < s2) {
            first.data = {static_cast<T>(0)};
            return first;
        }
        Polynomial ans(vector<T>(s1 - s2 + 1));
        for (ll i = ans.data.size() - 1; i >= 0; --i, --s1) {
            ans.data[i] = move(first[s1] * pow(second[s2], p - 2, p));
            first -= Polynomial(ans.data.begin(), ans.data.begin() + i + 1) * second;
        }
        return move(ans);
    }
    friend Polynomial<T> operator%(const Polynomial<T>& first,
                                    const Polynomial<T>& second) {
        return move(first - (first / second) * second);
    }
    void resize(ll n) {
        data.resize(n);
    }
};

ll char_to_ll(char symbol) {
    if (symbol >= 48 && symbol <= 57)
        return symbol - 48;
    if (symbol >= 65 && symbol <= 90)
        return symbol - 55;
    if (symbol >= 97 && symbol <= 122)
        return symbol - 61;
    if (symbol == 32)
        return 62;
    if (symbol == 46)
        return 63;
    return 64;
}
char ll_to_char(const ll& number) {
    if (number >= 0 && number <= 9)
        return static_cast<char>(number + 48);
    if (number >= 10 && number <= 35)
        return static_cast<char>(number + 55);
    if (number >= 36 && number <= 61)
        return static_cast<char>(number + 61);
    if (number == 62)
        return 32;
    if (number == 63) {
        return 46;
    }
    return '?';
}
bigint from_64_to_p(const string& words) {
    bigint ans(0);
    bigint t(1);
    for (const char& w : words) {
        ll sym = char_to_ll(w);
        ans += t * sym;
        t *= 64;
    }
    return ans;
}

string from_p_to_64(bigint h) {
    string ans;
    while (h != 0) {
        ll tmp = h % 64;
        char sym = ll_to_char(tmp);
        ans += sym;
        h /= 64;
    }
    return ans;
}
bigint merge(const vector<bigint>& h_i, const ll& p) {
    bigint tmp = bigint(0);
    bigint t = bigint(1);
    for (const auto& i : h_i) {
        tmp += i * t;
        t *= p;
    }
    return tmp;
}

vector<ll> partition(bigint& h, const ll& p, ll size){
    vector<ll> c;
    for (ll i = 0; i < size; ++i) {
        c.push_back(h % p);
        h /= p;
    }
    return c;
}

signed main() {
    cin >> p;
    string message;
    cin.ignore();
    getline(cin, message);
    stringstream ss(message);
    vector<ll> f, g, k;
    ll tmp;
    while(ss >> tmp)
        f.push_back(tmp);
    getline(cin, message);
    ss = stringstream(message);
    while(ss >> tmp)
        g.push_back(tmp);
    getline(cin, message);
    ss = stringstream(message);
    while (ss >> tmp)
        k.push_back(tmp);
    getline(cin, message);
    bigint h = from_64_to_p(message);
    ll size = f.size() - 1;
    Polynomial<ll> ff(move(f));
    Polynomial<ll> kk(move(k));
    Polynomial<ll> gg(move(g));
    Polynomial<ll> ordk = kk;
    ordk = ordk % ff;
    ordk.resize(size);
    Polynomial<ll> ordg = gg;
    ordg = ordg % ff;
    ordg.resize(size);
    while (h != 0) {
        vector<ll> h_i = partition(h, p, size);

        for (ll i = 0; i < size; ++i) {
            cout << ordg[i] << ' ';
        }
        cout << endl;
        Polynomial<ll> r_i(move(h_i));
        Polynomial<ll> ans = (r_i * ordk) % ff;
        for (ll i = 0; i < size; ++i) {
            cout << ans[i] << ' ';
        }
        cout << endl;
    }
}
