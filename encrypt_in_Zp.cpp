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

ll char_to_ll(const char& symbol) {
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

UInt change_notation(const string& words) {
    UInt ans(0);
    UInt t(1);
    for (const char& word : words) {
        ll sym = char_to_ll(word);
        ans += sym * t;
        t *= 64;
    }
    return ans;
}

void partitinon(UInt& h, const ll& p, vector<UInt>& h_i) {
    while (h >= 1) {
        h_i.push_back(h % p);
        h /= p;
    }
}

vector<ll> make_ords(const ll& g, const ll& p) {
    vector<ll> ans = {g};
    UInt g2 = (g * g) % p;
    while (g2 != g) {
        ans.push_back(g2 % p);
        g2 = (g2 * g) % p;
    }
    return ans;
}


signed main() {
    ll p, g, k;
    string message;
    cin >> p >> g >> k;
    cin.ignore();
    getline(cin, message);
    UInt h = change_notation(message);
    vector<UInt> h_i;
    partitinon(h, p, h_i);
    vector<ll> ords = make_ords(g, p);
    //ll b_i = p - 1;
    for (auto& i : h_i) {
        ll b_i = ords[rand() % p];
        cout << pow(g, b_i, p) << ' ';
        UInt mes = (i * (pow(k, b_i, p))) % p;
        cout << mes << '\n';
    }
}