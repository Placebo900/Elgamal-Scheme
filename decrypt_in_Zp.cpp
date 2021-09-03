#include<bits/stdc++.h>

#define int long long
#define pb push_back
#define sz(a) a.begin(),a.end()
#define x first
#define y second
#define endl '\n'
#define vout(a) for(auto u: a)cout<<u<<endl;
 
 
using namespace std;
 
typedef long long ll;
typedef unsigned long long ull;
typedef long double ld;
typedef double dd;
typedef pair<int, int> pii;
typedef pair<ll, ll> pll;
typedef pair<ld, ld> pld;
 
const int N = 2e6 + 23;

const long double PI = std::acos(-1.0L);

#include "long.h"

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

UInt merge(const ll& p, const vector<UInt>& h_i) {
    UInt tmp(0);
    UInt t(1);
    for (const auto& i : h_i) {
        tmp += i * t;
        t *= p;
    }
    return tmp;
}

string from_p_to_64(UInt& h) {
    string ans;
    while (h != 0) {
        ll tmp = h % 64;
        char sym = ll_to_char(tmp);
        ans += sym;
        h /= 64;
    }
    return ans;
}

signed main() {
    int p, k;
    cin >> p >> k;
    vector<UInt> h_i;
    int r_i, m_i;
    while (cin >> r_i >> m_i) {
        UInt decryptor = pow(UInt(r_i), p - 1 - k, p);
        decryptor = (m_i * decryptor) % p;
        h_i.push_back(decryptor);
    }
    UInt h = merge(p, h_i);
    string message = from_p_to_64(h);
    cout << message << '\n';
}