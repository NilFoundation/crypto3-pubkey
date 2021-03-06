//---------------------------------------------------------------------------//
// Copyright (c) 2018-2020 Mikhail Komarov <nemo@nil.foundation>
// Copyright (c) 2020 Ilias Khairullin <ilias@nil.foundation>
//
// MIT License
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//---------------------------------------------------------------------------//

#ifndef CRYPTO3_PUBKEY_SECRET_SHARING_SCHEME_STATE_HPP
#define CRYPTO3_PUBKEY_SECRET_SHARING_SCHEME_STATE_HPP

#include <boost/accumulators/accumulators.hpp>
#include <boost/accumulators/statistics/sum.hpp>

#include <boost/accumulators/framework/accumulator_set.hpp>
#include <boost/accumulators/framework/features.hpp>

#include <nil/crypto3/pubkey/accumulators/secret_sharing.hpp>

namespace nil {
    namespace crypto3 {
        namespace pubkey {
            template<typename Mode>
            using share_dealing_accumulator_set = boost::accumulators::accumulator_set<
                typename Mode::scheme_type::share_type,
                boost::accumulators::features<accumulators::tag::deal_share<Mode>>>;

            template<typename Scheme>
            using polynomial_recovering_accumulator_set =
                boost::accumulators::accumulator_set<typename Scheme::public_element_type,
                                                     boost::accumulators::features<boost::accumulators::tag::sum>>;

            template<typename Mode>
            using shares_dealing_accumulator_set = boost::accumulators::accumulator_set<
                typename Mode::scheme_type::shares_type,
                boost::accumulators::features<accumulators::tag::deal_shares<Mode>>>;

            template<typename Mode>
            using secret_reconstructing_accumulator_set = boost::accumulators::accumulator_set<
                typename Mode::scheme_type::private_element_type,
                boost::accumulators::features<accumulators::tag::reconstruct_secret<Mode>>>;

            template<typename Mode>
            using share_verification_accumulator_set = boost::accumulators::accumulator_set<
                bool, boost::accumulators::features<accumulators::tag::verify_share<Mode>>>;
        }    // namespace pubkey
    }        // namespace crypto3
}    // namespace nil

#endif    // CRYPTO3_PUBKEY_SECRET_SHARING_SCHEME_STATE_HPP
