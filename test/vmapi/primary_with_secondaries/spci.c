/*
 * Copyright 2019 The Hafnium Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "hf/spci.h"

#include <stdint.h>

#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "primary_with_secondary.h"
#include "test/hftest.h"
#include "test/vmapi/spci.h"

/**
 * Send a message to a secondary VM which checks the validity of the received
 * header.
 */
TEST(spci, msg_send)
{
	const char message[] = "spci_msg_send";
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM1, "spci_check", mb.send);

	/* Set the payload, init the message header and send the message. */
	memcpy_s(mb.send, SPCI_MSG_PAYLOAD_MAX, message, sizeof(message));
	EXPECT_EQ(
		spci_msg_send(HF_PRIMARY_VM_ID, SERVICE_VM1, sizeof(message), 0)
			.func,
		SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Send a message to a secondary VM spoofing the source VM id.
 */
TEST(spci, msg_send_spoof)
{
	const char message[] = "spci_msg_send";
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM1, "spci_check", mb.send);

	/* Set the payload, init the message header and send the message. */
	memcpy_s(mb.send, SPCI_MSG_PAYLOAD_MAX, message, sizeof(message));
	EXPECT_SPCI_ERROR(
		spci_msg_send(SERVICE_VM2, SERVICE_VM1, sizeof(message), 0),
		SPCI_INVALID_PARAMETERS);
}

/**
 * Send a message to a secondary VM with incorrect destination id.
 */
TEST(spci, spci_invalid_destination_id)
{
	const char message[] = "fail to send";
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM1, "spci_check", mb.send);
	/* Set the payload, init the message header and send the message. */
	memcpy_s(mb.send, SPCI_MSG_PAYLOAD_MAX, message, sizeof(message));
	EXPECT_SPCI_ERROR(
		spci_msg_send(HF_PRIMARY_VM_ID, -1, sizeof(message), 0),
		SPCI_INVALID_PARAMETERS);
}

/**
 * Ensure that the length parameter is respected when sending messages.
 */
TEST(spci, spci_incorrect_length)
{
	const char message[] = "this should be truncated";
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM1, "spci_length", mb.send);

	/* Send the message and compare if truncated. */
	memcpy_s(mb.send, SPCI_MSG_PAYLOAD_MAX, message, sizeof(message));
	/* Hard code incorrect length. */
	EXPECT_EQ(spci_msg_send(HF_PRIMARY_VM_ID, SERVICE_VM1, 16, 0).func,
		  SPCI_SUCCESS_32);
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Attempt to send a message larger than what is supported.
 */
TEST(spci, spci_large_message)
{
	const char message[] = "fail to send";
	struct mailbox_buffers mb = set_up_mailbox();

	memcpy_s(mb.send, SPCI_MSG_PAYLOAD_MAX, message, sizeof(message));
	/* Send a message that is larger than the mailbox supports (4KB). */
	EXPECT_SPCI_ERROR(
		spci_msg_send(HF_PRIMARY_VM_ID, SERVICE_VM1, 4 * 1024 + 1, 0),
		SPCI_INVALID_PARAMETERS);
}

/**
 * Verify secondary VM non blocking recv.
 */
TEST(spci, spci_recv_non_blocking)
{
	struct mailbox_buffers mb = set_up_mailbox();
	struct spci_value run_res;

	/* Check is performed in secondary VM. */
	SERVICE_SELECT(SERVICE_VM1, "spci_recv_non_blocking", mb.send);
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}
