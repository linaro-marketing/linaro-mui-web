import React from "react";
import { render } from "@testing-library/react";
import MegaMenuContent from "./MegaMenuContent";
import { MegaMenuContentProps } from "./MegaMenuContent.types";
describe("MegaMenuContent Test", () => {
  test("renders the MegaMenuContent component", () => {
    render(
      <MegaMenuContent
        content={{
          sections: [
            {
              title: "Automotive, IoT & Edge Devices",
              options: [
                {
                  title: "Client Devices",
                  pathname: "/client-devices/",
                },
                {
                  title: "Cloud Computing & Servers",
                  pathname: "/cloud-computing-and-servers/",
                },
              ],
            },
            {
              title: "Automotive, IoT & Edge Devices",
              options: [
                {
                  title: "Client Devices",
                  pathname: "/client-devices/",
                },
                {
                  title: "Cloud Computing & Servers",
                  pathname: "/cloud-computing-and-servers/",
                },
              ],
            },
          ],
        }}
      />
    );
  });
});
