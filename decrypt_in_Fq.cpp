#include <algorithm>
#include <bitset>
#include <cassert>
#include <complex>
#include <deque>
#include <exception>
#include <fstream>
#include <functional>
#include <iomanip>
#include <ios>
#include <iosfwd>
#include <iostream>
#include <istream>
#include <iterator>
#include <limits>
#include <list>
#include <locale>
#include <map>
#include <memory>
#include <new>
#include <numeric>
#include <ostream>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <stdexcept>
#include <streambuf>
#include <string>
#include <typeinfo>
#include <utility>
#include <valarray>
#include <vector>

using namespace std;
using cpx = complex<double>;
const double PI = acos(-1);
vector<cpx> roots = {{0, 0}, {1, 0}};

void ensure_capacity(int64_t min_capacity) {
    for (int64_t len = roots.size(); len < min_capacity; len *= 2) {
        for (int64_t i = len >> 1; i < len; i++) {
            roots.emplace_back(roots[i]);
            double angle = 2 * PI * (2 * i + 1 - len) / (len * 2);
            roots.emplace_back(cos(angle), sin(angle));
        }
    }
}

void fft(vector<cpx> &z, bool inverse) {
    int64_t n = z.size();
//    assert((n & (n - 1)) == 0);
    ensure_capacity(n);
    for (unsigned i = 1, j = 0; i < n; i++) {
        int64_t bit = n >> 1;
        for (; j >= bit; bit >>= 1)
            j -= bit;
        j += bit;
        if (i < j)
            swap(z[i], z[j]);
    }
    for (int64_t len = 1; len < n; len <<= 1) {
        for (int64_t i = 0; i < n; i += len * 2) {
            for (int64_t j = 0; j < len; j++) {
                cpx root = inverse ? conj(roots[j + len]) : roots[j + len];
                cpx u = z[i + j];
                cpx v = z[i + j + len] * root;
                z[i + j] = u + v;
                z[i + j + len] = u - v;
            }
        }
    }
    if (inverse)
        for (int64_t i = 0; i < n; i++)
            z[i] /= n;
}

vector<int64_t> multiply_bigint(const vector<int64_t> &a, const vector<int64_t> &b, int64_t base) {
    int64_t need = a.size() + b.size();
    int64_t n = 1;
    while (n < need)
        n <<= 1;
    vector<cpx> p(n);
    for (size_t i = 0; i < n; i++) {
        p[i] = cpx(i < a.size() ? a[i] : 0, i < b.size() ? b[i] : 0);
    }
    fft(p, false);
    // a[w[k]] = (p[w[k]] + conj(p[w[n-k]])) / 2
    // b[w[k]] = (p[w[k]] - conj(p[w[n-k]])) / (2*i)
    vector<cpx> ab(n);
    cpx r(0, -0.25);
    for (int64_t i = 0; i < n; i++) {
        int64_t j = (n - i) & (n - 1);
        ab[i] = (p[i] * p[i] - conj(p[j] * p[j])) * r;
    }
    fft(ab, true);
    vector<int64_t> result(need);
    int64_t carry = 0;
    for (int64_t i = 0; i < need; i++) {
        int64_t d = (int64_t)(ab[i].real() + 0.5) + carry;
        carry = d / base;
        result[i] = d % base;
    }
    return result;
}

vector<int64_t> multiply_mod(const vector<int64_t> &a, const vector<int64_t> &b, int64_t m) {
    int64_t need = a.size() + b.size() - 1;
    int64_t n = 1;
    while (n < need)
        n <<= 1;
    vector<cpx> A(n);
    for (size_t i = 0; i < a.size(); i++) {
        int64_t x = (a[i] % m + m) % m;
        A[i] = cpx(x & ((1 << 15) - 1), x >> 15);
    }
    fft(A, false);

    vector<cpx> B(n);
    for (size_t i = 0; i < b.size(); i++) {
        int64_t x = (b[i] % m + m) % m;
        B[i] = cpx(x & ((1 << 15) - 1), x >> 15);
    }
    fft(B, false);

    vector<cpx> fa(n);
    vector<cpx> fb(n);
    for (int64_t i = 0, j = 0; i < n; i++, j = n - i) {
        cpx a1 = (A[i] + conj(A[j])) * cpx(0.5, 0);
        cpx a2 = (A[i] - conj(A[j])) * cpx(0, -0.5);
        cpx b1 = (B[i] + conj(B[j])) * cpx(0.5, 0);
        cpx b2 = (B[i] - conj(B[j])) * cpx(0, -0.5);
        fa[i] = a1 * b1 + a2 * b2 * cpx(0, 1);
        fb[i] = a1 * b2 + a2 * b1;
    }

    fft(fa, true);
    fft(fb, true);
    vector<int64_t> res(need);
    for (int64_t i = 0; i < need; i++) {
        int64_t aa = (int64_t)(fa[i].real() + 0.5);
        int64_t bb = (int64_t)(fb[i].real() + 0.5);
        int64_t cc = (int64_t)(fa[i].imag() + 0.5);
        res[i] = (aa % m + (bb % m << 15) + (cc % m << 30)) % m;
    }
    return res;
}
constexpr int64_t digits(int64_t base) noexcept {
    return base <= 1 ? 0 : 1 + digits(base / 10);
}

constexpr int64_t base = 1000'000'000;
constexpr int64_t base_digits = digits(base);

constexpr int64_t fft_base = 10'000;  // fft_base^2 * n / fft_base_digits <= 10^15 for double
constexpr int64_t fft_base_digits = digits(fft_base);

struct bigint {
    // value == 0 is represented by empty z
    vector<int64_t> z = {0};  // digits

    // sign == 1 <==> value >= 0
    // sign == -1 <==> value < 0
    int64_t sign;

    bigint(int64_t v = 0) { *this = v; }

    bigint &operator=(int64_t v) {
        sign = v < 0 ? -1 : 1;
        v *= sign;
        z.clear();
        for (; v > 0; v = v / base)
            z.push_back((int64_t)(v % base));
        return *this;
    }

    bigint(const string &s) { read(s); }

    bigint &operator+=(const bigint &other) {
        if (sign == other.sign) {
            for (int64_t i = 0, carry = 0; i < other.z.size() || carry; ++i) {
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
                for (int64_t i = 0, carry = 0; i < other.z.size() || carry; ++i) {
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

    bigint &operator*=(int64_t v) {
        if (v < 0)
            sign = -sign, v = -v;
        for (int64_t i = 0, carry = 0; i < z.size() || carry; ++i) {
            if (i == z.size())
                z.push_back(0);
            int64_t cur = (int64_t)z[i] * v + carry;
            carry = (int64_t)(cur / base);
            z[i] = (int64_t)(cur % base);
        }
        trim();
        return *this;
    }

    bigint operator*(int64_t v) const { return bigint(*this) *= v; }

    friend pair<bigint, bigint> divmod(const bigint &a1, const bigint &b1) {
        int64_t norm = base / (b1.z.back() + 1);
        bigint a = a1.abs() * norm;
        bigint b = b1.abs() * norm;
        bigint q, r;
        q.z.resize(a.z.size());

        for (int64_t i = (int64_t)a.z.size() - 1; i >= 0; i--) {
            r *= base;
            r += a.z[i];
            int64_t s1 = b.z.size() < r.z.size() ? r.z[b.z.size()] : 0;
            int64_t s2 = b.z.size() - 1 < r.z.size() ? r.z[b.z.size() - 1] : 0;
            int64_t d = (int64_t)(((int64_t)s1 * base + s2) / b.z.back());
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

        int64_t n = a.z.size();

        int64_t firstDigit = (int64_t)::sqrt((double)a.z[n - 1] * base + a.z[n - 2]);
        int64_t norm = base / (firstDigit + 1);
        a *= norm;
        a *= norm;
        while (a.z.empty() || a.z.size() % 2 == 1)
            a.z.push_back(0);

        bigint r = (int64_t)a.z[n - 1] * base + a.z[n - 2];
        firstDigit = (int64_t)::sqrt((double)a.z[n - 1] * base + a.z[n - 2]);
        int64_t q = firstDigit;
        bigint res;

        for (int64_t j = n / 2 - 1; j >= 0; j--) {
            for (;; --q) {
                bigint r1 = (r - (res * 2 * base + q) * q) * base * base +
                            (j > 0 ? (int64_t)a.z[2 * j - 1] * base + a.z[2 * j - 2] : 0);
                if (r1 >= 0) {
                    r = r1;
                    break;
                }
            }
            res *= base;
            res += q;

            if (j > 0) {
                int64_t d1 = res.z.size() + 2 < r.z.size() ? r.z[res.z.size() + 2] : 0;
                int64_t d2 = res.z.size() + 1 < r.z.size() ? r.z[res.z.size() + 1] : 0;
                int64_t d3 = res.z.size() < r.z.size() ? r.z[res.z.size()] : 0;
                q = (int64_t)(((int64_t)d1 * base * base + (int64_t)d2 * base + d3) / (firstDigit * 2));
            }
        }

        res.trim();
        return res / norm;
    }

    bigint operator/(const bigint &v) const { return divmod(*this, v).first; }

    bigint operator%(const bigint &v) const { return divmod(*this, v).second; }

    bigint &operator/=(int64_t v) {
        if (v < 0)
            sign = -sign, v = -v;
        for (int64_t i = (int64_t)z.size() - 1, rem = 0; i >= 0; --i) {
            int64_t cur = z[i] + rem * (int64_t)base;
            z[i] = (int64_t)(cur / v);
            rem = (int64_t)(cur % v);
        }
        trim();
        return *this;
    }

    bigint operator/(int64_t v) const { return bigint(*this) /= v; }

    int64_t operator%(int64_t v) const {
        if (v < 0)
            v = -v;
        int64_t m = 0;
        for (int64_t i = (int64_t)z.size() - 1; i >= 0; --i)
            m = (int64_t)((z[i] + m * (int64_t)base) % v);
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
        for (int64_t i = (int64_t)z.size() - 1; i >= 0; i--)
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

    int64_t longValue() const {
        int64_t res = 0;
        for (int64_t i = (int64_t)z.size() - 1; i >= 0; i--)
            res = res * base + z[i];
        return res * sign;
    }

    friend bigint gcd(const bigint &a, const bigint &b) { return b.isZero() ? a : gcd(b, a % b); }

    friend bigint lcm(const bigint &a, const bigint &b) { return a / gcd(a, b) * b; }

    void read(const string &s) {
        sign = 1;
        z.clear();
        int64_t pos = 0;
        while (pos < s.size() && (s[pos] == '-' || s[pos] == '+')) {
            if (s[pos] == '-')
                sign = -sign;
            ++pos;
        }
        for (int64_t i = (int64_t)s.size() - 1; i >= pos; i -= base_digits) {
            int64_t x = 0;
            for (int64_t j = max(pos, i - base_digits + 1); j <= i; j++)
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
        for (int64_t i = (int64_t)v.z.size() - 2; i >= 0; --i)
            stream << setw(base_digits) << setfill('0') << v.z[i];
        return stream;
    }

    static vector<int64_t> convert_base(const vector<int64_t> &a, int64_t old_digits, int64_t new_digits) {
        vector<int64_t> p(max(old_digits, new_digits) + 1);
        p[0] = 1;
        for (int64_t i = 1; i < p.size(); i++)
            p[i] = p[i - 1] * 10;
        vector<int64_t> res;
        int64_t cur = 0;
        int64_t cur_digits = 0;
        for (int64_t v : a) {
            cur += v * p[cur_digits];
            cur_digits += old_digits;
            while (cur_digits >= new_digits) {
                res.push_back(int64_t(cur % p[new_digits]));
                cur /= p[new_digits];
                cur_digits -= new_digits;
            }
        }
        res.push_back((int64_t)cur);
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
        for (int64_t i = 0; i < z.size(); ++i)
            if (z[i])
                for (int64_t j = 0, carry = 0; j < v.z.size() || carry; ++j) {
                    int64_t cur = res.z[i + j] + (int64_t)z[i] * (j < v.z.size() ? v.z[j] : 0) + carry;
                    carry = (int64_t)(cur / base);
                    res.z[i + j] = (int64_t)(cur % base);
                }
        res.trim();
        return res;
    }
};


inline int64_t char_to_number(char symbol) {
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

bigint getNum64Base(const std::string& words) {
    bigint res(0), shift(1);
    for (const auto& letter : words) {
        res += shift * char_to_number(letter);
        shift *= 64;
    }
    return res;
}

char digit_to_char(int64_t number) {
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
// Возведение в степень:
int64_t pow(int64_t a, int64_t n, int64_t p) {
    int64_t res(1);
    while (n > 0) {
        if (n % 2 != 0)
            res = (res * a) % p;
        a = (a * a) % p;
        n /= 2;
    }
    return res % p;
}
bigint combine(int64_t p, const std::vector<int64_t>& nums) {
    bigint res(0), shift(1);
    for (const auto& num : nums) {
        res += shift * num;
        shift *= p;
    }
    return res;
}
template<typename T>
class Polynomial;
template<typename T>
std::ostream& operator<<(std::ostream& out, const Polynomial<T>& p) {
    for (int i = p.Degree(); i > 0; --i) {
        if (p[i] != static_cast<T>(0)) {
            (p[i] != T(1) && p[i] != T(-1)) ? out << p[i] << '*': out << (p[i] == T(-1) ? "-" : "");
            (i > 1) ? out << "x^" << i : out << "x";
        }
        out << (p[i - 1] > static_cast<T>(0) ? "+" : "");
    }
    return (p.Degree() == -1 ? out << 0 : (p[0] != static_cast<T>(0) ? out << p[0] : out));
}

static int64_t p;
#include <utility>
template<typename T>
class Polynomial {
private:
    std::vector<T> data;

public:
    explicit Polynomial(std::vector<T>&& v) : data(std::move(v)) {}
    explicit Polynomial(std::vector<T>& v) : data(std::move(v)) {}
    template<typename It>
    explicit Polynomial(const It& begin, const It& end) : data(begin, end) {}

    [[nodiscard]] int Degree() const {
        auto pred = [](const T& x) { return x != static_cast<T>(0); };
        auto i = data.rend() - std::find_if(data.rbegin(), data.rend(), pred);
        return (i ? i - 1 : -1);
    }
    Polynomial&operator+=(const Polynomial& other) {
        data.resize(std::max(other.Degree(), Degree()) + 1);
        for (size_t i = 0; i < data.size(); ++i) {
            data[i] = (data[i] + other[i]) % p;
        }
        return *this;
    }
    friend Polynomial operator+(Polynomial first, const Polynomial& second) {
        return std::move(first += second);
    }
    Polynomial&operator-=(const Polynomial& other) {
        data.resize(std::max(other.Degree(), Degree()) + 1);
        for (size_t i = 0; i < data.size(); ++i) {
            data[i] = (data[i] - other[i]) % p;
        }
        return *this;
    }
    friend Polynomial operator-(Polynomial first, const Polynomial& second) {
        return std::move(first -= second);
    }
    friend bool operator==(const Polynomial& first, const Polynomial& second) {
        auto deg1 = first.Degree() + 1;
        auto deg2 = second.Degree() + 1;
        auto it1 = first.data.begin();
        auto it2 = second.data.begin();
        return deg1 == deg2 && std::includes(it1, it1 + deg1, it2, it2+ deg2);
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
        std::vector<T> ans(s1 + s2 - 1);
        for (int64_t i = 0; i < s1; ++i) {
            for (int64_t j = 0; j < s2; ++j) {
                ans[i + j] = (ans[i + j] + data[i] * other.data[j]) % p;
            }
        }
        data = std::move(ans);
        return *this;
    }
    friend Polynomial operator*(Polynomial first, const Polynomial& second) {
        return std::move(first *= second);
    }
    friend Polynomial<T> operator/(Polynomial first, Polynomial second) {
        auto s1 = first.Degree();
        auto s2 = second.Degree();
        if (s1 == -1 || s2 == -1 || s1 < s2) {
            first.data = {static_cast<T>(0)};
            return first;
        }
        Polynomial ans(std::vector<T>(s1 - s2 + 1));
        for (int64_t i = ans.data.size() - 1; i >= 0; --i, --s1) {
            ans.data[i] = std::move(first[s1] * pow(second[s2], p - 2, p));
            first -= Polynomial(ans.data.begin(), ans.data.begin() + i + 1) * second;
        }
        return std::move(ans);
    }
    friend Polynomial<T> operator%(const Polynomial<T>& first,
                                    const Polynomial<T>& second) {
        return std::move(first - (first / second) * second);
    }

    Polynomial<T> inv(const Polynomial<T>& f) const {
        Polynomial<int64_t> r1(*this), r2(f);
        Polynomial<int64_t> y1({1}), y2({0});
        while (r1.Degree() > 0) {
            Polynomial<int64_t> q = r2 / r1, r0 = r2 - r1 * q;
            r2 = r1;
            r1 = r0;
            Polynomial<int64_t> y0 = y2 - y1 * q;
            y2 = y1;
            y1 = y0;
        }
        Polynomial<int64_t> tmp = (*this * y1) % f;
        assert(tmp.Degree() == 0);
        tmp.data[0] = pow(tmp[0], p - 2, p);
        return tmp * y1 % f;
    }
    Polynomial<int64_t> power(uint32_t n, const Polynomial<int64_t>& f) {
        Polynomial<int64_t> res({1}), value(*this);
        while (n > 0) {
            if (n % 2 != 0)
                res *= value;
            value *= value;
            n /= 2;
        }
        return std::move(res);
    }
    void resize(uint32_t n) {
        data.resize(n);
    }
};


static uint32_t n;
void combine(bigint& msg, bigint& shift, const Polynomial<int64_t>& nums) {
    for (int64_t i = 0; i < n; ++i) {
        msg += shift * nums[i];
        shift *= p;
    }
}
int main() {
    std::cin >> p;
    std::string input_str;
    std::cin.ignore();
    getline(std::cin, input_str);
    std::istringstream in(input_str);
    std::vector<int64_t> v;
    int64_t x;
    while (in >> x) {
        v.emplace_back(x);
    }
    n = v.size() - 1;
    Polynomial<int64_t> f(v);
    uint32_t k;
    std::cin >> k;
    std::cin.ignore();
    bigint msg(0), shift(1);
    while (getline(std::cin, input_str)) {
        std::vector<int64_t> r_i, m_i;
        in = std::istringstream(input_str);
        while (in >> x) {
            r_i.emplace_back(x);
        }
        getline(std::cin, input_str);
        in = std::istringstream(input_str);
        while (in >> x) {
            m_i.emplace_back(x);
        }
        Polynomial<int64_t> tmp = Polynomial<int64_t>(r_i).power(k) % f;
        assert((tmp * tmp.inv(f) % f).Degree() == 0);
        Polynomial<int64_t> h_i = (Polynomial<int64_t>(m_i) * tmp.inv(f)) % f;
        combine(msg, shift, h_i);
    }
    while (msg != 0) {
        long long ans = abs(msg % 64);
        std::cout << digit_to_char(ans);
        msg /= 64;
    }
    std::cout << std::endl;
    return 0;
}
//
//// Man I l0ve fishing. Man I l0ve fishing. Man I l0ve fishing.
//// 0Fa3xxtiwLuQt4x7GFsjpmR7pCSq5J Dcza6Qi1kQzmHoAYrz95Jv7hing.