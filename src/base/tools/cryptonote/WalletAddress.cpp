/* XMRig
 * Copyright (c) 2012-2013 The Cryptonote developers
 * Copyright (c) 2014-2021 The Monero Project
 * Copyright (c) 2018-2023 SChernykh   <https://github.com/SChernykh>
 * Copyright (c) 2016-2023 XMRig       <https://github.com/xmrig>, <support@xmrig.com>
 *
 *   This program is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program. If not, see <http://www.gnu.org/licenses/>.
 */

#include "base/tools/cryptonote/WalletAddress.h"
#include "3rdparty/rapidjson/document.h"
#include "base/crypto/keccak.h"
#include "base/tools/Buffer.h"
#include "base/tools/cryptonote/BlobReader.h"
#include "base/tools/cryptonote/umul128.h"
#include "base/tools/Cvt.h"

#if defined(_MSC_VER)
static inline bool __builtin_add_overflow(uint64_t a, uint64_t b, uint64_t *out) {
    *out = a + b;
    return *out < a;
}
#endif


#include <array>
#include <map>
#include <vector>

// Base58 alphabet for Tari address decoding
static constexpr const char *base58_alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

// Reverse lookup table for Base58 (initialized once, thread-safe under C++11+).
static const int8_t *base58_reverse()
{
    static const int8_t *rev = [] {
        auto *table = new int8_t[256];
        memset(table, -1, sizeof(int8_t) * 256);
        for (size_t i = 0; base58_alphabet[i]; ++i) {
            table[static_cast<uint8_t>(base58_alphabet[i])] = static_cast<int8_t>(i);
        }
        return table;
    }();
    return rev;
}

// Base58 decoder for Tari addresses
// Simple multiply-accumulate: result = result * 58 + digit, using uint64_t chunks.
static bool base58_decode(const char *input, size_t len, std::vector<uint8_t> &output)
{

    output.clear();
    if (len == 0) return true;

    const int8_t *rev = base58_reverse();

    // Count leading zeros (characters that map to value 0, i.e., '1')
    size_t zero_count = 0;
    while (zero_count < len && rev[static_cast<uint8_t>(input[zero_count])] == 0) {
        ++zero_count;
    }

    // Multiply-accumulate: result *= 58, then add digit
    // Store as array of uint64_t chunks (little-endian order within each chunk)
    std::vector<uint64_t> chunks(1, 0);

    for (size_t i = zero_count; i < len; ++i) {
        const int8_t digit = rev[static_cast<uint8_t>(input[i])];
        if (digit < 0) return false;

        uint64_t carry = static_cast<uint64_t>(digit);
        for (size_t j = 0; j < chunks.size(); ++j) {
            uint64_t hi;
            const uint64_t lo = __umul128(chunks[j], 58, &hi);
            if (__builtin_add_overflow(lo, carry, &chunks[j])) {
                carry = hi + 1;
            } else {
                carry = hi;
            }
        }
        if (carry) {
            chunks.push_back(carry);
        }
    }

    // Convert to bytes: each chunk is little-endian, so extract MSB first
    std::vector<uint8_t> raw;
    for (int c = static_cast<int>(chunks.size()) - 1; c >= 0; --c) {
        uint64_t num = chunks[c];
        for (int b = 7; b >= 0; --b) {
            raw.push_back(static_cast<uint8_t>((num >> (b * 8)) & 0xFF));
        }
    }

    // Trim leading zeros, then restore zero_count
    size_t first = 0;
    while (first < raw.size() && raw[first] == 0) ++first;
    for (size_t i = first; i < raw.size(); ++i) output.push_back(raw[i]);
    if (zero_count > 0) {
        const size_t insert_count = (zero_count <= output.size() + 7) ? zero_count : output.size() + 7;
        output.insert(output.begin(), insert_count, 0);
    }

    return true;
}


bool xmrig::WalletAddress::decode(const char *address, size_t size)
{
    uint64_t tf_tag = 0;
    if (size >= 4 && !strncmp(address, "TF", 2)) {
      tf_tag = 0x424200;
      switch (address[2])
      {
        case '1': tf_tag |= 0; break;
        case '2': tf_tag |= 1; break;
        default: tf_tag = 0; return false;
      }
      switch (address[3]) {
        case 'M': tf_tag |= 0; break;
        case 'T': tf_tag |= 0x10; break;
        case 'S': tf_tag |= 0x20; break;
        default: tf_tag = 0; return false;
      }
      address += 4;
      size -= 4;
    }

    // Tari addresses start with specific 2-character prefixes:
    // First char encodes network byte: '1'=0x00 (MainNet), 'f'=0x26 (Esmeralda)
    // Second char encodes feature byte, looked up via the shared Base58 reverse table.
    uint8_t net_byte = 0;
    if (size >= 2 && address[0] == 'f') {
        net_byte = 0x26; // Esmeralda
    } else if (size >= 2 && address[0] == '1') {
        net_byte = 0x00; // MainNet
    }

    if (net_byte != 0 || address[0] == '1') {
        uint8_t feat_byte = static_cast<uint8_t>(base58_reverse()[static_cast<uint8_t>(address[1])]);
        m_tag = static_cast<uint64_t>(net_byte << 8 | feat_byte);
        address += 2;
        size -= 2;

        // For Tari addresses, decode remaining characters using Base58
        const char *rest_address = address;
        size_t rest_size = size;

        std::vector<uint8_t> rest_data;
        if (!base58_decode(rest_address, rest_size, rest_data)) {
            return false;
        }

        // Tari addresses: network(1) + features(1) + view_key(32) + spend_key(32) + checksum(1) = 67 bytes
        const size_t expected_data_size = 67;  // network + features + view + spend + checksum

        if (rest_data.size() != expected_data_size - 2) {
            return false;
        }

        Buffer data;
        data.reserve(expected_data_size);
        data.emplace_back(net_byte);
        data.emplace_back(feat_byte);

        for (auto b : rest_data) {
            data.emplace_back(b);
        }

        const size_t data_size = data.size();
        uint8_t checksum = data.back();
        const uint8_t *spend_key = data.data() + 34;   // offset 34: after network(1), features(1), and view_key(32)
        const uint8_t *view_key = data.data() + 2;     // offset 2: after network and features

        // Verify checksum using DammSum algorithm
        uint8_t computed_checksum = 0;
        for (size_t i = 0; i < data_size - 1; ++i) {
            computed_checksum ^= data[i];
            bool overflow = (computed_checksum & 0x80) != 0;
            computed_checksum = static_cast<uint8_t>((computed_checksum << 1) & 0xFF);
            if (overflow) {
                computed_checksum ^= 0x1B;  // Damm mask
            }
        }

        if (checksum != computed_checksum) {
            return false;
        }

        // Map Tari network byte to XMRig Net type for tag construction
        // MainNet (0x00) → MAINNET, Esmeralda/TestNet (0x26/0x10) → TESTNET, StageNet (0x01) → STAGENET
        uint8_t tari_net_type = 0;
        if (net_byte == 0x00) tari_net_type = 0;       // MAINNET
        else if (net_byte == 0x26 || net_byte == 0x10) tari_net_type = 1;  // TESTNET/Esmeralda
        else if (net_byte == 0x01) tari_net_type = 2;  // STAGENET

        m_tag = static_cast<uint64_t>(tari_net_type) | (static_cast<uint64_t>(feat_byte) << 8);
        memcpy(m_publicViewKey, view_key, 32);
        memcpy(m_publicSpendKey, spend_key, 32);
        memset(m_checksum, 0, sizeof(m_checksum));
        m_checksum[0] = checksum;
        m_data = String(address, size);

        return true;
    }

    static constexpr std::array<int, 9> block_sizes{ 0, 2, 3, 5, 6, 7, 9, 10, 11 };
    static constexpr char alphabet[] = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    constexpr size_t alphabet_size = sizeof(alphabet) - 1;

    if (size < kMinSize || size > kMaxSize) {
        return false;
    }

    int8_t reverse_alphabet[256];
    memset(reverse_alphabet, -1, sizeof(reverse_alphabet));

    for (size_t i = 0; i < alphabet_size; ++i) {
        reverse_alphabet[static_cast<int>(alphabet[i])] = i;
    }

    const int len = static_cast<int>(size);
    const int num_full_blocks = len / block_sizes.back();
    const int last_block_size = len % block_sizes.back();

    int last_block_size_index = -1;

    for (size_t i = 0; i < block_sizes.size(); ++i) {
        if (block_sizes[i] == last_block_size) {
            last_block_size_index = i;
            break;
        }
    }

    if (last_block_size_index < 0) {
        return false;
    }

    const size_t data_size = static_cast<size_t>(num_full_blocks) * sizeof(uint64_t) + last_block_size_index;
    if (data_size < kMinDataSize) {
        return false;
    }

    Buffer data;
    data.reserve(data_size);

    const char *address_data = address;

    for (int i = 0; i <= num_full_blocks; ++i) {
        uint64_t num = 0;
        uint64_t order = 1;

        for (int j = ((i < num_full_blocks) ? block_sizes.back() : last_block_size) - 1; j >= 0; --j) {
            const int digit = reverse_alphabet[static_cast<int>(address_data[j])];
            if (digit < 0) {
                return false;
            }

            uint64_t hi;
            const uint64_t tmp = num + __umul128(order, static_cast<uint64_t>(digit), &hi);
            if ((tmp < num) || hi) {
                return false;
            }

            num = tmp;
            order *= alphabet_size;
        }

        address_data += block_sizes.back();

        auto p = reinterpret_cast<const uint8_t*>(&num);
        for (int j = ((i < num_full_blocks) ? static_cast<int>(sizeof(num)) : last_block_size_index) - 1; j >= 0; --j) {
            data.emplace_back(p[j]);
        }
    }

    assert(data.size() == data_size);

    BlobReader<false> ar(data.data(), data_size);

    if (ar(m_tag) && ar(m_publicSpendKey) && ar(m_publicViewKey) && ar.skip(ar.remaining() - sizeof(m_checksum)) && ar(m_checksum)) {
        uint8_t md[200];
        keccak(data.data(), data_size - sizeof(m_checksum), md);

        if (memcmp(m_checksum, md, sizeof(m_checksum)) == 0) {
            m_data = { address, size };

            if (tf_tag) {
              m_tag = tf_tag;
            }

            return true;
        }
    }

    m_tag = 0;

    return false;
}


bool xmrig::WalletAddress::decode(const rapidjson::Value &address)
{
    return address.IsString() && decode(address.GetString(), address.GetStringLength());
}


const char *xmrig::WalletAddress::netName() const
{
    static const std::array<const char *, 3> names = { "mainnet", "testnet", "stagenet" };

    return names[net()];
}


const char *xmrig::WalletAddress::typeName() const
{
    static const std::array<const char *, 3> names = { "public", "integrated", "subaddress" };

    return names[type()];
}


rapidjson::Value xmrig::WalletAddress::toJSON(rapidjson::Document &doc) const
{
    using namespace rapidjson;

    return isValid() ? m_data.toJSON(doc) : Value(kNullType);
}


#ifdef XMRIG_FEATURE_API
rapidjson::Value xmrig::WalletAddress::toAPI(rapidjson::Document &doc) const
{
    using namespace rapidjson;

    if (!isValid()) {
        return Value(kNullType);
    }

    auto &allocator = doc.GetAllocator();
    Value out(kObjectType);
    out.AddMember(StringRef(Coin::kField),  coin().toJSON(), allocator);
    out.AddMember("address",                m_data.toJSON(doc), allocator);
    out.AddMember("type",                   StringRef(typeName()), allocator);
    out.AddMember("net",                    StringRef(netName()), allocator);
    out.AddMember("rpc_port",               rpcPort(), allocator);
    out.AddMember("zmq_port",               zmqPort(), allocator);
    out.AddMember("tag",                    m_tag, allocator);
    out.AddMember("view_key",               Cvt::toHex(m_publicViewKey, kKeySize, doc), allocator);
    out.AddMember("spend_key",              Cvt::toHex(m_publicSpendKey, kKeySize, doc), allocator);
    out.AddMember("checksum",               Cvt::toHex(m_checksum, sizeof(m_checksum), doc), allocator);

    return out;
}
#endif


const xmrig::WalletAddress::TagInfo &xmrig::WalletAddress::tagInfo(uint64_t tag)
{
    static TagInfo dummy = { Coin::INVALID, MAINNET, PUBLIC, 0, 0 };

    static const std::map<uint64_t, TagInfo> tags = {
        { 0x12,     { Coin::MONERO,     MAINNET,    PUBLIC,         18081,  18082 } },
        { 0x13,     { Coin::MONERO,     MAINNET,    INTEGRATED,     18081,  18082 } },
        { 0x2a,     { Coin::MONERO,     MAINNET,    SUBADDRESS,     18081,  18082 } },

        { 0x35,     { Coin::MONERO,     TESTNET,    PUBLIC,         28081,  28082 } },
        { 0x36,     { Coin::MONERO,     TESTNET,    INTEGRATED,     28081,  28082 } },
        { 0x3f,     { Coin::MONERO,     TESTNET,    SUBADDRESS,     28081,  28082 } },

        { 0x18,     { Coin::MONERO,     STAGENET,   PUBLIC,         38081,  38082 } },
        { 0x19,     { Coin::MONERO,     STAGENET,   INTEGRATED,     38081,  38082 } },
        { 0x24,     { Coin::MONERO,     STAGENET,   SUBADDRESS,     38081,  38082 } },

        { 0x2bb39a, { Coin::SUMO,       MAINNET,    PUBLIC,         19734,  19735 } },
        { 0x29339a, { Coin::SUMO,       MAINNET,    INTEGRATED,     19734,  19735 } },
        { 0x8319a,  { Coin::SUMO,       MAINNET,    SUBADDRESS,     19734,  19735 } },

        { 0x37751a, { Coin::SUMO,       TESTNET,    PUBLIC,         29734,  29735 } },
        { 0x34f51a, { Coin::SUMO,       TESTNET,    INTEGRATED,     29734,  29735 } },
        { 0x1d351a, { Coin::SUMO,       TESTNET,    SUBADDRESS,     29734,  29735 } },

        { 0x2cca,   { Coin::ARQMA,      MAINNET,    PUBLIC,         19994,  19995 } },
        { 0x116bc7, { Coin::ARQMA,      MAINNET,    INTEGRATED,     19994,  19995 } },
        { 0x6847,   { Coin::ARQMA,      MAINNET,    SUBADDRESS,     19994,  19995 } },

        { 0x53ca,   { Coin::ARQMA,      TESTNET,    PUBLIC,         29994,  29995 } },
        { 0x504a,   { Coin::ARQMA,      TESTNET,    INTEGRATED,     29994,  29995 } },
        { 0x524a,   { Coin::ARQMA,      TESTNET,    SUBADDRESS,     29994,  29995 } },

        { 0x39ca,   { Coin::ARQMA,      STAGENET,   PUBLIC,         39994,  39995 } },
        { 0x1742ca, { Coin::ARQMA,      STAGENET,   INTEGRATED,     39994,  39995 } },
        { 0x1d84ca, { Coin::ARQMA,      STAGENET,   SUBADDRESS,     39994,  39995 } },

        { 0x1032,   { Coin::WOWNERO,    MAINNET,    PUBLIC,         34568,  34569 } },
        { 0x1a9a,   { Coin::WOWNERO,    MAINNET,    INTEGRATED,     34568,  34569 } },
        { 0x2fb0,   { Coin::WOWNERO,    MAINNET,    SUBADDRESS,     34568,  34569 } },

        { 0x5a,     { Coin::GRAFT,      MAINNET,    PUBLIC,         18981,  18982 } },
        { 0x5b,     { Coin::GRAFT,      MAINNET,    INTEGRATED,     18981,  18982 } },
        { 0x66,     { Coin::GRAFT,      MAINNET,    SUBADDRESS,     18981,  18982 } },

        { 0x54,     { Coin::GRAFT,      TESTNET,    PUBLIC,         28881,  28882 } },
        { 0x55,     { Coin::GRAFT,      TESTNET,    INTEGRATED,     28881,  28882 } },
        { 0x70,     { Coin::GRAFT,      TESTNET,    SUBADDRESS,     28881,  28882 } },

        { 0x424200,     { Coin::TOWNFORGE,     MAINNET,    PUBLIC,         18881,  18882 } },
        { 0x424201,     { Coin::TOWNFORGE,     MAINNET,    SUBADDRESS,     18881,  18882 } },

        { 0x424210,     { Coin::TOWNFORGE,     TESTNET,    PUBLIC,         28881,  28882 } },
        { 0x424211,     { Coin::TOWNFORGE,     TESTNET,    SUBADDRESS,     28881,  28882 } },

        { 0x424220,     { Coin::TOWNFORGE,     STAGENET,   PUBLIC,         38881,  38882 } },
        { 0x424221,     { Coin::TOWNFORGE,     STAGENET,   SUBADDRESS,     38881,  38882 } },

        // Tari network tags (tari_net_type | (feat_byte << 8))
        { 0x0100,     { Coin::TARI,       MAINNET,    PUBLIC,         9000,   9001 } },
        { 0x0101,     { Coin::TARI,       MAINNET,    INTEGRATED,     9000,   9001 } },
        { 0x0102,     { Coin::TARI,       MAINNET,    SUBADDRESS,     9000,   9001 } },

        { 0x0103,     { Coin::TARI,       TESTNET,    PUBLIC,         9000,   9001 } },
        { 0x0104,     { Coin::TARI,       TESTNET,    INTEGRATED,     9000,   9001 } },
        { 0x0105,     { Coin::TARI,       TESTNET,    SUBADDRESS,     9000,   9001 } },

        { 0x0201,     { Coin::TARI,       STAGENET,   PUBLIC,         9000,   9001 } },
        { 0x0202,     { Coin::TARI,       STAGENET,    INTEGRATED,     9000,   9001 } },
        { 0x0203,     { Coin::TARI,       STAGENET,   SUBADDRESS,     9000,   9001 } },

    };

    const auto it = tags.find(tag);

    return it == tags.end() ? dummy : it->second;
}
